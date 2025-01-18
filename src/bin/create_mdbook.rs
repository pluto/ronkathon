/// Read SUMMARY.md and copy `README.md` files given in it from `src` to `book` directory.
/// Additionally, change the links to other `README.md` files to `index.md`, so that link
/// points to correct file in the mdbook.
use std::{
  fs::{self, File},
  io::{self, BufRead, BufReader, Write},
  path::{Path, PathBuf},
};

use regex::Regex;

const DEST: &str = "book";

fn main() -> io::Result<()> {
  let dest_path = Path::new(DEST);
  if !dest_path.exists() {
    fs::create_dir(dest_path)?;
  }

  let mut readmes = Vec::<PathBuf>::new();
  let f = File::open("SUMMARY.md")?;
  let reader = BufReader::new(f);

  let re = Regex::new(r"\[.*\]\((.*)\)").unwrap();

  for line in reader.lines() {
    for (_, [link]) in re.captures_iter(&line?).map(|c| c.extract()) {
      if !link.is_empty() {
        readmes.push(PathBuf::from(link));
      }
    }
  }

  let readme_re = Regex::new(r"README.md").unwrap();

  for src in &readmes {
    println!("Working on: {}", src.display());

    let dest = Path::new(DEST).join(src);
    let dest_folder = dest.parent().unwrap();
    if !dest_folder.exists() {
      fs::create_dir_all(dest_folder)?;
    }
    let src_file = File::open(src)?;
    let reader = BufReader::new(src_file);

    let mut dest_file = File::create(&dest)?;

    for line in reader.lines() {
      let before = line.unwrap();
      let after = readme_re.replace_all(&before, "index.md");
      dest_file.write_all(after.as_bytes())?;
      dest_file.write_all(b"\n")?;
    }
  }

  println!("Copying SUMMARY.md to {DEST}/SUMMARY.md");
  fs::copy("SUMMARY.md", "book/SUMMARY.md")?;

  println!("Done!");

  Ok(())
}
