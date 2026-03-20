use crate::state::AppState;
use anyhow::{Error, Result};
use reqwest::header::CONTENT_TYPE;
use serde::{Deserialize, Serialize};
use std::sync::Mutex;
use tauri::State;
use pasta_curves::{group::ff::PrimeField as _, Fp};
use zcash_vote::{
    address::VoteAddress,
    db::{list_notes, load_prop},
    decrypt::{to_fvk, to_sk},
    election::{BALLOT_PK, BALLOT_VK},
    trees::{list_cmxs, compute_nf_tree, prepare_nullifiers, compute_nf_proof},
};

#[tauri::command]
pub fn get_sync_height(state: State<'_, Mutex<AppState>>) -> Result<Option<u32>, String> {
    tauri_export!(state, connection, {
        let height = load_prop(&connection, "height")?.map(|h| h.parse::<u32>().unwrap());
        Ok::<_, Error>(height)
    })
}

#[tauri::command]
pub fn get_available_balance(state: State<'_, Mutex<AppState>>) -> Result<u64, String> {
    tauri_export!(state, connection, {
        let balance = connection.query_row(
            "SELECT SUM(value) FROM notes WHERE spent IS NULL",
            [],
            |r| r.get::<_, Option<u64>>(0),
        )?;
        Ok::<_, Error>(balance.unwrap_or_default())
    })
}

#[tauri::command]
pub async fn vote(
    address: String,
    amount: u64,
    state: State<'_, Mutex<AppState>>,
) -> Result<String, String> {
    let r = async {
        let (pool, base_urls, sk, fvk, scope, domain, signature_required) = {
            let state = state.lock().unwrap();
            let pool = state.pool.clone();
            let base_urls = state.urls.clone();
            let sk = to_sk(&state.key)?;
            let fvk = to_fvk(&state.key)?;
            let scope = state.scope;
            let domain = state.election.domain();
            let signature_required = state.election.signature_required;
            (pool, base_urls, sk, fvk, scope, domain, signature_required)
        };
        let mut rng = rand_core::OsRng;
        let vaddress = VoteAddress::decode(&address)?;
        let connection = pool.get()?;
        let notes = list_notes(&connection, 0, &fvk, scope)?;
        let cmxs = list_cmxs(&connection)?;

        // Build NF tree locally and compute proofs for each note's nullifier.
        // TODO: Replace with PIR client query for privacy.
        let extra = {
            let mut s = connection.prepare("SELECT hash FROM nfs")?;
            let rows = s.query_map([], |r| {
                let v = r.get::<_, [u8; 32]>(0)?;
                let v = Fp::from_repr(v).unwrap();
                Ok(v)
            })?;
            rows.collect::<Result<Vec<_>, _>>()?
        };
        let sorted_nfs = prepare_nullifiers(extra);
        let (nf_root, ranges, levels) = compute_nf_tree(sorted_nfs);

        // Compute NF non-membership proofs for each input note
        let mut nf_proofs = vec![];
        for (note, _pos) in notes.iter() {
            let nf = note.nullifier(&fvk);
            let nf_fp = Fp::from_repr(nf.to_bytes()).unwrap();
            let proof = compute_nf_proof(nf_fp, nf_root, &ranges, &levels)
                .ok_or_else(|| anyhow::anyhow!("Nullifier is in the set — cannot vote"))?;
            nf_proofs.push(orchard::vote::NfProofData {
                root: proof.root,
                low: proof.low,
                width: proof.width,
                leaf_pos: proof.leaf_pos,
                path: proof.path,
            });
        }

        let ballot = orchard::vote::vote(
            domain,
            signature_required,
            sk,
            &fvk,
            vaddress.0,
            amount,
            &notes,
            &nf_proofs,
            &cmxs,
            &mut rng,
            &BALLOT_PK,
            &BALLOT_VK,
        )?;

        let client = reqwest::Client::new();
        let mut hash = String::new();
        let mut error = String::new();
        let mut success = false;
        for base_url in base_urls.iter() {
            let url = format!("{}/ballot", base_url);
            let rep = client
                .post(url)
                .header(CONTENT_TYPE, "application/json")
                .json(&ballot)
                .send()
                .await?;
            let s = rep.status().is_success();
            let res = rep.text().await?;
            if s {
                success = true;
            }
            else {
                tracing::info!("ERROR (transient): {error}");
                error = res;
                continue;
            }

            if hash.is_empty() {
                hash = hex::encode(ballot.data.sighash()?);
                crate::db::store_vote(&connection, &hash, &address, amount)?;
            }
        }
        if !success {
            anyhow::bail!(error);
        }
        Ok::<_, Error>(hash)
    };

    r.await.map_err(|e| e.to_string())
}

#[tauri::command]
pub fn fetch_votes(state: State<'_, Mutex<AppState>>) -> Result<Vec<Vote>, String> {
    tauri_export!(state, connection, {
        let mut s = connection
            .prepare("SELECT id_vote, hash, address, amount FROM votes ORDER BY id_vote")?;
        let rows = s.query_map([], |r| {
            Ok((
                r.get::<_, u32>(0)?,
                r.get::<_, String>(1)?,
                r.get::<_, String>(2)?,
                r.get::<_, u64>(3)?,
            ))
        })?;
        let mut votes = vec![];
        for r in rows {
            let (id_vote, hash, address, amount) = r?;
            votes.push(Vote {
                id: id_vote,
                hash,
                address,
                amount,
            })
        }
        Ok::<_, Error>(votes)
    })
}

#[derive(Clone, Serialize, Deserialize, Debug)]
pub struct Vote {
    pub id: u32,
    pub hash: String,
    pub address: String,
    pub amount: u64,
}
