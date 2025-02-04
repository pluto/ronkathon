use ronkathon::tree::merkle::*;

fn main() {
  let values = ["a", "b", "c", "d", "e", "f", "g", "h"];
  let leaves = values.iter().map(|v| v.to_string()).collect();
  let tree = MerkleTree::new(leaves);

  println!("{tree}");

  let proof = tree.get_proof(2);
  println!("Proof for index 2:\n{}", proof);
}
