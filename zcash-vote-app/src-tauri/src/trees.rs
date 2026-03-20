use std::sync::Mutex;

use anyhow::{Error, Result};
use orchard::vote::calculate_merkle_paths;
use pasta_curves::group::ff::PrimeField as _;
use rusqlite::Connection;
use tauri::State;
use zcash_vote::{
    db::{load_prop, store_prop},
    trees::list_cmxs,
};

use crate::state::AppState;

#[tauri::command]
pub fn compute_roots(state: State<Mutex<AppState>>) -> Result<(), String> {
    tauri_export!(state, connection, {
        if load_prop(&connection, "height")?.is_some() {
            compute_nf_root(&connection)?;
            compute_cmx_root(&connection)?;
        }
        Ok::<_, Error>(())
    })
}

pub fn compute_nf_root(connection: &Connection) -> Result<Vec<u8>> {
    let nf_root = zcash_vote::trees::compute_nf_root(connection)?;
    store_prop(connection, "nf_root", &hex::encode(&nf_root.0))?;
    Ok(nf_root.0.to_vec())
}

// TODO: Retrieve frontier
pub fn compute_cmx_root(connection: &Connection) -> Result<Vec<u8>> {
    let cmx_tree = list_cmxs(connection)?;
    let (cmx_root, _) = calculate_merkle_paths(0, &[], &cmx_tree);
    store_prop(connection, "cmx_root", &hex::encode(&cmx_root.to_repr()))?;

    Ok(cmx_root.to_repr().to_vec())
}
