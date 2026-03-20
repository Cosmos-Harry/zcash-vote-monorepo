use anyhow::Result;
use ff::Field as _;
use orchard::vote::{calculate_merkle_paths, poseidon_hash, Frontier, OrchardHash};
use pasta_curves::{group::ff::PrimeField as _, Fp};
use rusqlite::Connection;

/// Depth of the Poseidon-based nullifier range Merkle tree.
/// Matches the PIR tree depth (imt-tree crate).
pub const NF_TREE_DEPTH: usize = 29;

/// A gap range `[low, width]` representing an interval between two adjacent
/// on-chain nullifiers. `low` is the interval start and `width = high - low`.
pub type NfRange = [Fp; 2];

/// Pre-computed proof data for a nullifier non-membership proof.
/// This is what the circuit needs to verify that a nullifier is NOT in the set.
#[derive(Clone, Debug)]
pub struct NfProofData {
    pub root: Fp,
    pub low: Fp,
    pub width: Fp,
    pub leaf_pos: u32,
    pub path: [Fp; NF_TREE_DEPTH],
}

// ---------------------------------------------------------------------------
// NF range tree (Poseidon-based, replaces old Sinsemilla-based NF tree)
// ---------------------------------------------------------------------------

/// Build gap ranges from sorted nullifiers using `[low, width]` format.
///
/// For each gap between consecutive nullifiers, emits `[low, width]` where
/// `width = high - low` (inclusive bounds). Matches `imt-tree::build_nf_ranges`.
pub fn build_nf_ranges(nfs: impl IntoIterator<Item = Fp>) -> Vec<NfRange> {
    let mut prev = Fp::zero();
    let mut ranges = vec![];
    for r in nfs {
        if prev < r {
            let high = r - Fp::one();
            ranges.push([prev, high - prev]);
        }
        prev = r + Fp::one();
    }
    if prev != Fp::zero() {
        let high = Fp::one().neg();
        ranges.push([prev, high - prev]);
    }
    ranges
}

/// Inject 17 sentinel nullifiers at `k * 2^250` for `k = 0..=16` to ensure
/// all gap widths are bounded below `2^250` (required by the circuit's
/// range check constraint). Matches `imt-tree::build_sentinel_tree`.
pub fn prepare_nullifiers(extra: Vec<Fp>) -> Vec<Fp> {
    let step = Fp::from(2u64).pow([250, 0, 0, 0]);
    let mut nfs: Vec<Fp> = (0u64..=16).map(|k| step * Fp::from(k)).collect();
    nfs.extend(extra);
    nfs.sort();
    nfs
}

/// Pre-compute the empty subtree hash at each tree level.
///
/// `empty[0] = poseidon(0, 0)` — the commitment of an empty leaf.
/// `empty[i] = poseidon(empty[i-1], empty[i-1])` — a fully empty subtree.
pub fn precompute_empty_hashes() -> [Fp; NF_TREE_DEPTH] {
    let mut empty = [Fp::default(); NF_TREE_DEPTH];
    empty[0] = poseidon_hash(Fp::zero(), Fp::zero());
    for i in 1..NF_TREE_DEPTH {
        empty[i] = poseidon_hash(empty[i - 1], empty[i - 1]);
    }
    empty
}

/// Hash each `[low, width]` range into a leaf commitment via `poseidon(low, width)`.
pub fn commit_ranges(ranges: &[NfRange]) -> Vec<Fp> {
    ranges
        .iter()
        .map(|[low, width]| poseidon_hash(*low, *width))
        .collect()
}

/// Build a Poseidon Merkle tree bottom-up from leaf hashes.
///
/// Returns `(root, levels)` where `levels[i]` contains node hashes at level `i`.
/// Level 0 = leaf commitments (padded to even length).
pub fn build_levels(mut leaves: Vec<Fp>, empty: &[Fp; NF_TREE_DEPTH]) -> (Fp, Vec<Vec<Fp>>) {
    let mut levels: Vec<Vec<Fp>> = Vec::with_capacity(NF_TREE_DEPTH);

    if leaves.is_empty() {
        leaves.push(empty[0]);
    }
    if leaves.len() & 1 == 1 {
        leaves.push(empty[0]);
    }
    levels.push(leaves);

    for i in 0..NF_TREE_DEPTH - 1 {
        let prev = &levels[i];
        let pairs = prev.len() / 2;
        let mut next: Vec<Fp> = (0..pairs)
            .map(|j| poseidon_hash(prev[j * 2], prev[j * 2 + 1]))
            .collect();
        if next.len() & 1 == 1 {
            next.push(empty[i + 1]);
        }
        levels.push(next);
    }

    let top = &levels[NF_TREE_DEPTH - 1];
    let root = poseidon_hash(top[0], top[1]);

    (root, levels)
}

/// Find the gap-range index that contains `value`.
///
/// Returns `Some(i)` where `ranges[i]` is `[low, width]` and `value - low <= width`,
/// or `None` if the value is an existing nullifier.
pub fn find_range_for_value(ranges: &[NfRange], value: Fp) -> Option<usize> {
    let i = ranges.partition_point(|[low, _]| *low <= value);
    if i == 0 {
        return None;
    }
    let idx = i - 1;
    let [low, width] = ranges[idx];
    let offset = value - low;
    if offset <= width {
        Some(idx)
    } else {
        None
    }
}

/// Build the full NF tree from sorted nullifiers (with sentinels already injected).
///
/// Returns `(root, ranges, levels)`.
pub fn compute_nf_tree(nfs: Vec<Fp>) -> (Fp, Vec<NfRange>, Vec<Vec<Fp>>) {
    let ranges = build_nf_ranges(nfs);
    let leaves = commit_ranges(&ranges);
    let empty = precompute_empty_hashes();
    let (root, levels) = build_levels(leaves, &empty);
    (root, ranges, levels)
}

/// Generate a non-membership proof for `value` given pre-computed tree data.
///
/// Returns `Some(NfProofData)` if `value` falls within a gap range,
/// or `None` if `value` is an existing nullifier.
pub fn compute_nf_proof(
    value: Fp,
    root: Fp,
    ranges: &[NfRange],
    levels: &[Vec<Fp>],
) -> Option<NfProofData> {
    let idx = find_range_for_value(ranges, value)?;
    let empty = precompute_empty_hashes();

    let mut path = [Fp::zero(); NF_TREE_DEPTH];
    let mut pos = idx;
    for (level, sibling_hash) in path.iter_mut().enumerate().take(NF_TREE_DEPTH) {
        let sibling = pos ^ 1;
        *sibling_hash = if sibling < levels[level].len() {
            levels[level][sibling]
        } else {
            empty[level]
        };
        pos >>= 1;
    }

    let [low, width] = ranges[idx];
    Some(NfProofData {
        root,
        low,
        width,
        leaf_pos: idx as u32,
        path,
    })
}

// ---------------------------------------------------------------------------
// Database-backed helpers
// ---------------------------------------------------------------------------

/// Load nullifiers from DB, inject sentinels, build ranges.
pub fn list_nf_ranges(connection: &Connection) -> Result<(Vec<NfRange>, Vec<Fp>)> {
    let mut s = connection.prepare("SELECT hash FROM nfs")?;
    let rows = s.query_map([], |r| {
        let v = r.get::<_, [u8; 32]>(0)?;
        let v = Fp::from_repr(v).unwrap();
        Ok(v)
    })?;
    let extra = rows.collect::<std::result::Result<Vec<_>, _>>()?;
    let nfs = prepare_nullifiers(extra);
    let ranges = build_nf_ranges(nfs);
    Ok((ranges, vec![]))
}

/// Compute the NF tree root from the DB.
pub fn compute_nf_root(connection: &Connection) -> Result<OrchardHash> {
    let mut s = connection.prepare("SELECT hash FROM nfs")?;
    let rows = s.query_map([], |r| {
        let v = r.get::<_, [u8; 32]>(0)?;
        let v = Fp::from_repr(v).unwrap();
        Ok(v)
    })?;
    let extra = rows.collect::<std::result::Result<Vec<_>, _>>()?;
    let nfs = prepare_nullifiers(extra);
    let (root, _, _) = compute_nf_tree(nfs);
    Ok(OrchardHash(root.to_repr()))
}

// ---------------------------------------------------------------------------
// CMX tree (unchanged — still uses Sinsemilla/MerkleHashOrchard)
// ---------------------------------------------------------------------------

pub fn list_cmxs(connection: &Connection) -> Result<Vec<Fp>> {
    let mut s = connection.prepare("SELECT hash FROM cmxs ORDER BY id_cmx")?;
    let rows = s.query_map([], |r| {
        let v = r.get::<_, [u8; 32]>(0)?;
        let v = Fp::from_repr(v).unwrap();
        Ok(v)
    })?;
    let cmx_tree = rows.collect::<std::result::Result<Vec<_>, _>>()?;
    Ok(cmx_tree)
}

pub fn compute_cmx_root(connection: &Connection) -> Result<(OrchardHash, Option<Frontier>)> {
    let cmx_tree = list_cmxs(connection)?;
    let (cmx_root, frontier) = if cmx_tree.is_empty() {
        let (cmx_root, _) = calculate_merkle_paths(0, &[], &[]);
        (cmx_root, None)
    } else {
        let end_position = cmx_tree.len() - 1;
        let leaf = cmx_tree[end_position];
        let (cmx_root, mps) = calculate_merkle_paths(0, &[end_position as u32], &cmx_tree);
        let mp = &mps[0];
        let ommers = mp
            .path
            .iter()
            .map(|o| OrchardHash(o.to_repr()))
            .collect::<Vec<_>>();

        let frontier = Frontier {
            position: mp.position,
            leaf: OrchardHash(leaf.to_repr()),
            ommers,
        };
        (cmx_root, Some(frontier))
    };
    Ok((OrchardHash(cmx_root.to_repr()), frontier))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use ff::Field;

    #[test]
    fn test_poseidon_hash_known_vectors() {
        // Frozen test vectors from imt-tree/src/tree/tests.rs
        // These MUST match to ensure tree compatibility with the PIR system.

        let check = |left: Fp, right: Fp, expected_hex: &str| {
            let h = poseidon_hash(left, right);
            let hex = hex::encode(h.to_repr());
            assert_eq!(hex, expected_hex, "Poseidon({left:?}, {right:?}) mismatch");
        };

        check(
            Fp::zero(),
            Fp::zero(),
            "7a515983cec6c21e27c2f24fbc31c54d698400d33300ebc7f4677cb71b529403",
        );

        check(
            Fp::one(),
            Fp::from(2u64),
            "4ce3bd9407dc758983c62390ce00463beb82796eb0d40a0398993cb4eca55535",
        );

        check(
            Fp::from(42u64),
            Fp::zero(),
            "fad8a97bb5213839cff67906a2d74baa2b889ae882b3c44f3c0721c7edadaf3d",
        );

        check(
            Fp::from(0xDEAD_BEEFu64),
            Fp::from(0xCAFE_BABEu64),
            "c2f13f05353ed3b31f348fd82539ed31649c8d31ee12ea0f9da8c22ba1c5b724",
        );

        // p - 1 (the largest field element)
        let p_minus_1 = Fp::zero() - Fp::one();
        check(
            p_minus_1,
            Fp::one(),
            "576b8132d0cba1b8232040b6f89a15e52ef26ada02dda96709f3212a9234d414",
        );
    }

    #[test]
    fn test_build_nf_ranges_basic() {
        let nfs = vec![Fp::from(10u64), Fp::from(20u64), Fp::from(30u64)];
        let ranges = build_nf_ranges(nfs);

        // Should produce 4 ranges:
        // [0, 9] -> [0, 9]
        // [11, 19] -> [11, 8]
        // [21, 29] -> [21, 8]
        // [31, MAX] -> [31, MAX-31]
        assert_eq!(ranges.len(), 4);

        assert_eq!(ranges[0][0], Fp::zero()); // low = 0
        assert_eq!(ranges[0][1], Fp::from(9u64)); // width = 9

        assert_eq!(ranges[1][0], Fp::from(11u64)); // low = 11
        assert_eq!(ranges[1][1], Fp::from(8u64)); // width = 8

        assert_eq!(ranges[2][0], Fp::from(21u64)); // low = 21
        assert_eq!(ranges[2][1], Fp::from(8u64)); // width = 8
    }

    #[test]
    fn test_sentinel_injection() {
        let nfs = prepare_nullifiers(vec![]);
        // 17 sentinels at k * 2^250 for k=0..=16
        assert_eq!(nfs.len(), 17);
        assert_eq!(nfs[0], Fp::zero());

        let step = Fp::from(2u64).pow([250, 0, 0, 0]);
        assert_eq!(nfs[1], step);
        assert_eq!(nfs[16], step * Fp::from(16u64));
    }

    #[test]
    fn test_sentinel_tree_all_ranges_under_2_250() {
        let nfs = prepare_nullifiers(vec![Fp::from(100u64), Fp::from(200u64), Fp::from(300u64)]);
        let ranges = build_nf_ranges(nfs);

        for (i, [_low, width]) in ranges.iter().enumerate() {
            let repr = width.to_repr();
            assert!(
                repr.as_ref()[31] < 0x04,
                "range {i} has width >= 2^250"
            );
        }
    }

    #[test]
    fn test_find_range_for_value() {
        let nfs = vec![Fp::from(10u64), Fp::from(20u64)];
        let ranges = build_nf_ranges(nfs);

        // Value 5 should be in range [0, 9]
        assert!(find_range_for_value(&ranges, Fp::from(5u64)).is_some());

        // Value 15 should be in range [11, 8]
        assert!(find_range_for_value(&ranges, Fp::from(15u64)).is_some());

        // Nullifier 10 should NOT be in any range
        assert!(find_range_for_value(&ranges, Fp::from(10u64)).is_none());

        // Nullifier 20 should NOT be in any range
        assert!(find_range_for_value(&ranges, Fp::from(20u64)).is_none());
    }

    #[test]
    fn test_compute_nf_tree_and_proof() {
        let nfs = prepare_nullifiers(vec![Fp::from(100u64), Fp::from(200u64)]);
        let (root, ranges, levels) = compute_nf_tree(nfs);

        // Value 150 is not a nullifier — should get a valid proof
        let proof = compute_nf_proof(Fp::from(150u64), root, &ranges, &levels);
        assert!(proof.is_some());
        let proof = proof.unwrap();
        assert_eq!(proof.root, root);

        // Verify the proof: recompute root from leaf + path
        let leaf_hash = poseidon_hash(proof.low, proof.width);
        let mut current = leaf_hash;
        let mut pos = proof.leaf_pos as usize;
        for sibling in &proof.path {
            if pos & 1 == 0 {
                current = poseidon_hash(current, *sibling);
            } else {
                current = poseidon_hash(*sibling, current);
            }
            pos >>= 1;
        }
        assert_eq!(current, root, "Merkle proof verification failed");

        // Nullifier 100 should NOT produce a proof
        let proof = compute_nf_proof(Fp::from(100u64), root, &ranges, &levels);
        assert!(proof.is_none());
    }

    #[test]
    fn test_empty_tree() {
        let nfs = prepare_nullifiers(vec![]);
        let (root, ranges, levels) = compute_nf_tree(nfs);

        // Should still produce valid ranges from sentinels
        assert!(!ranges.is_empty());

        // A random value should produce a valid proof
        let proof = compute_nf_proof(Fp::from(42u64), root, &ranges, &levels);
        assert!(proof.is_some());
    }

    #[test]
    fn test_cross_implementation_root_matches_pir() {
        // This root was computed by imt-tree's build_sentinel_tree(&[10,20,30,40])
        // from the vote-nullifier-pir repo. If this test fails, our Poseidon tree
        // implementation diverges from the PIR server's and proofs won't verify.
        let expected_root_hex =
            "d949e6646d367c9a7803a29a5687ea2a0af243e1c62ded678e739d497b442537";
        let expected_bytes: [u8; 32] = hex::decode(expected_root_hex)
            .unwrap()
            .try_into()
            .unwrap();
        let expected_root = Fp::from_repr(expected_bytes).unwrap();

        let nfs = vec![
            Fp::from(10u64),
            Fp::from(20u64),
            Fp::from(30u64),
            Fp::from(40u64),
        ];
        let sorted = prepare_nullifiers(nfs);
        let (root, _ranges, _levels) = compute_nf_tree(sorted);

        assert_eq!(
            root, expected_root,
            "Root mismatch with PIR repo (imt-tree). Our implementation diverges."
        );
    }
}
