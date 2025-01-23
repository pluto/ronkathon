//! A very basic Merkle tree data structure with means of building and checking proofs.

use crate::hashes::sha::Sha256;

/// A very basic Merkle tree data structure.
#[derive(Debug)]
pub struct MerkleTree {
  leaves: Vec<String>,
  hashes: Vec<Vec<[u8; 32]>>,
}

/// An enum to represent whether a neighboring hash value should be on the left or right side of the
/// current hash value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LeftOrRight {
  /// Neighboring hash value is on the left side.
  Left,

  /// Neighboring hash value is on the right side.
  Right,
}

/// A proof that a given value is in a Merkle tree which can be verified by a Merkle tree by calling
/// the [`MerkleTree::prove`] method.
#[derive(Debug, Clone)]
pub struct Proof(Vec<([u8; 32], LeftOrRight)>);

impl MerkleTree {
  /// Creates a new Merkle tree from a list of leaf values.
  #[allow(clippy::new_without_default)]
  pub fn new(leaves: Vec<String>) -> Self {
    let hashfunc = Sha256::new();
    let mut hashes = vec![];
    let leaf_hashes: Vec<[u8; 32]> =
      leaves.iter().map(|leaf| hashfunc.digest(leaf.as_bytes()).try_into().unwrap()).collect();
    let mut branch_nodes = leaf_hashes.clone();
    hashes.push(leaf_hashes);

    // Pair up leaf hashes and hash them together to make the next level of the tree
    while branch_nodes.len() > 1 {
      let mut new_branch_nodes = vec![];
      let chunks = branch_nodes.chunks_exact(2);
      let remainder = chunks.remainder();
      for chunk in chunks {
        let combined = [chunk[0].as_slice(), chunk[1].as_slice()].concat();
        let hash = hashfunc.digest(&combined).try_into().unwrap();
        new_branch_nodes.push(hash);
      }
      if remainder.len() == 1 {
        let combined = [remainder[0].as_slice(), remainder[0].as_slice()].concat();
        let hash = hashfunc.digest(&combined).try_into().unwrap();
        new_branch_nodes.push(hash);
      }
      hashes.push(new_branch_nodes.clone());
      branch_nodes = new_branch_nodes;
    }

    hashes.reverse();
    MerkleTree { leaves, hashes }
  }

  /// Returns the root hash of the Merkle tree.
  pub fn root_hash(&self) -> [u8; 32] { self.hashes[0][0] }

  /// Returns a [`Proof`] that a given leaf value is in the Merkle tree.
  pub fn get_proof(&self, leaf_index: usize) -> Proof {
    let mut proof = vec![];
    let mut index = leaf_index;

    // Start at the leaves and work our way up to the root
    for level in self.hashes.iter().skip(1).rev() {
      let (sibling_parity, sibling_index) = if index % 2 == 0 {
        (LeftOrRight::Right, index + 1)
      } else {
        (LeftOrRight::Left, index - 1)
      };
      proof.push((level[sibling_index], sibling_parity));
      index /= 2;
    }
    Proof(proof)
  }

  /// Verifies a [`Proof`] that a given `value` is in the Merkle tree.
  pub fn prove(&self, value: String, proof: Proof) -> bool {
    let hashfunc = Sha256::new();
    let mut hash = hashfunc.digest(value.as_bytes());

    for (sibling_hash, position) in proof.0.into_iter() {
      let combined = if position == LeftOrRight::Left {
        [sibling_hash.as_slice(), hash.as_slice()].concat()
      } else {
        [hash.as_slice(), sibling_hash.as_slice()].concat()
      };
      hash = hashfunc.digest(&combined);
    }

    hash == self.root_hash()
  }
}

impl std::fmt::Display for MerkleTree {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    let mut tree_str = String::new();

    // Print the leaves
    tree_str.push_str("Leaves:\n");
    for (i, leaf) in self.leaves.iter().enumerate() {
      tree_str.push_str(&format!("  {}: {}\n", i, leaf));
    }

    // Print the hashes
    for (level, hashes) in self.hashes.iter().enumerate().rev() {
      if hashes.len() == 1 {
        tree_str.push_str("Root Hash:\n");
        tree_str.push_str(&format!("  {}\n", hex::encode(hashes[0])));
      } else {
        tree_str.push_str(&format!("Level {}:\n", level));
        for hash in hashes {
          tree_str.push_str(&format!("  {}\n", hex::encode(hash)));
        }
      }
    }

    write!(f, "{}", tree_str)
  }
}

impl std::fmt::Display for Proof {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    let mut proof_str = String::new();

    for x in self.0.iter() {
      proof_str.push_str(&format!("{:?}", (hex::encode(x.0), x.1)));
    }
    write!(f, "{proof_str}")
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn even_leaf_tree() {
    let leaves = vec!["a".to_string(), "b".to_string(), "c".to_string(), "d".to_string()];
    let tree = MerkleTree::new(leaves);
    println!("{}", tree);
    assert_eq!(tree.hashes.len(), 3);
    assert_eq!(tree.hashes[0].len(), 1);
    assert_eq!(tree.hashes[1].len(), 2);
    assert_eq!(tree.hashes[2].len(), 4);
  }

  #[test]
  fn odd_leaf_tree() {
    let leaves =
      vec!["a".to_string(), "b".to_string(), "c".to_string(), "d".to_string(), "e".to_string()];
    let tree = MerkleTree::new(leaves);
    println!("{}", tree);
    assert_eq!(tree.hashes.len(), 4);
    assert_eq!(tree.hashes[0].len(), 1);
    assert_eq!(tree.hashes[1].len(), 2);
    assert_eq!(tree.hashes[2].len(), 3);
    assert_eq!(tree.hashes[3].len(), 5);
  }

  #[test]
  fn test_different_value() {
    let tree1 = MerkleTree::new(vec![
      "a".to_string(),
      "b".to_string(),
      "c".to_string(),
      "d".to_string(),
      "e".to_string(),
    ]);
    let tree2 = MerkleTree::new(vec![
      "a".to_string(),
      "b".to_string(),
      "c".to_string(),
      "d".to_string(),
      "f".to_string(),
    ]);
    let tree3 = MerkleTree::new(vec![
      "b".to_string(),
      "a".to_string(),
      "c".to_string(),
      "d".to_string(),
      "e".to_string(),
    ]);
    assert_ne!(tree1.root_hash(), tree2.root_hash());
    assert_ne!(tree1.root_hash(), tree3.root_hash());
    assert_ne!(tree2.root_hash(), tree3.root_hash());
  }

  #[test]
  fn proof_siblings() {
    let leaves = vec!["a".to_string(), "b".to_string(), "c".to_string(), "d".to_string()];
    let tree = MerkleTree::new(leaves);
    println!("{}", tree);

    // Get a proof for "b" (index 1)
    let proof = tree.get_proof(1);
    println!(
      "{:?}",
      proof.0.iter().map(|x| (hex::encode(x.0), x.1)).collect::<Vec<(String, LeftOrRight)>>()
    );
  }

  #[test]
  fn valid_proof() {
    let leaves = vec!["a".to_string(), "b".to_string(), "c".to_string(), "d".to_string()];
    let tree = MerkleTree::new(leaves);
    println!("{}", tree);

    // Get a proof for "b" (index 1)
    let proof = tree.get_proof(1);
    assert!(tree.prove("b".to_string(), proof));
  }

  #[test]
  #[should_panic]
  fn invalid_proof_wrong_element() {
    let leaves = vec!["a".to_string(), "b".to_string(), "c".to_string(), "d".to_string()];
    let tree = MerkleTree::new(leaves);
    println!("{}", tree);

    // Get a proof for "b" (index 1)
    let proof = tree.get_proof(1);
    // Use proof for "b" to prove "a"
    assert!(tree.prove("a".to_string(), proof));
  }

  #[test]
  #[should_panic]
  fn invalid_proof_wrong_sibling() {
    let leaves = vec!["a".to_string(), "b".to_string(), "c".to_string(), "d".to_string()];
    let tree = MerkleTree::new(leaves);
    println!("{}", tree);

    // Get a proof for "b" (index 1)
    let mut proof = tree.get_proof(1);
    // Modify the sibling hash to make the proof invalid
    proof.0[0].0 = [0u8; 32];
    assert!(tree.prove("b".to_string(), proof));
  }
}
