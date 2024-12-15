use ronkathon::tree::merkle::*;

fn main(){
    // let leaves = vec!["a".to_string(), "b".to_string(), "c".to_string(), 
    //                   "d".to_string(), "e".to_string(), "f".to_string(),
    //                   "g".to_string(), "h".to_string()];

    let values = vec!["a", "b", "c", "d", "e", "f", "g", "h"];
    let leaves = values.iter().map(|v| v.to_string()).collect();
    let tree = MerkleTree::new(leaves);

    println!("{tree}");

    let proof = tree.get_proof(2);
    println!("Proof for index 2:\n{}", proof);
}
