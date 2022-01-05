pub use blake2b_simd::{Hash as Blake2bHash, Params as Blake2bParams};
pub use primitive_types::*;
pub use crate::level_generator::GeometricalLevelGenerator;
use chain_common::digest::Digestible;
pub use std::{vec, vec::Vec, collections::{BTreeMap, BTreeSet}};
use crate::skipnode::SkipNode;
use serde::{Deserialize, Serialize};

/*
impl Digestible for [u8] {
    fn to_digest(&self) -> H256 {
        let mut hasher = Blake2bParams::new();
        hasher.hash_length(32);
        hasher.to_state().update(self);
        H256::from_slice(hasher.to_state().finalize().as_bytes())
    }
}

impl Digestible for Vec<u8> {
    fn to_digest(&self) -> H256 {
        self.as_slice().to_digest()
    }
}

impl Digestible for usize {
    fn to_digest(&self) -> H256 {
        self.to_le_bytes().to_digest()
    }
}
*/



////
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Proof<V: Digestible + Clone + Default> {
    pub root: H256,
    pub subproof: SubProof<V>,
}

///
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct SubProof<V: Digestible + Clone + Default> {
    pub nodes: Vec<SkipNode<V>>,
    pub values: Vec<Option<V>>,
    pub nodehash: Vec<H256>,
}

///
impl<V: Digestible + Clone + Default> SubProof<V> {
    pub fn new (nodes: Vec<SkipNode<V>>, values: Vec<Option<V>>, nodehash: Vec<H256>) -> SubProof<V> {
        SubProof {
            nodes: nodes,
            values: values,
            nodehash: nodehash,
        }
    }
}