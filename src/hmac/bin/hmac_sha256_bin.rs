use std::env;

use ronkathon::hmac::hmac_sha256::hmac_sha256;

fn main() {
  // Get command-line arguments
  let args: Vec<String> = env::args().collect();

  // Check if an input was provided
  if args.len() < 2 {
    eprintln!("Please provide an input argument.");
    std::process::exit(1);
  }

  // Pass the first argument to the function
  let key = args[1].as_bytes();
  let message = args[2].as_bytes();
  let result = hex::encode(hmac_sha256(key, message));

  println!("Result: {}", result);
}
