/// 1. Read SUMMARY.md and copy `README.md` files given in it to `book` directory.
/// 2. Change the links to other `README.md` files to `index.md`, so that link points to
///    correct file in the mdbook.
/// 3. Change links that point to a '.rs' file to their github repo link.
use std::{
  fs::{self, File},
  io::{self, BufRead, BufReader, Write},
  path::{Path, PathBuf},
};

use regex::Regex;

const DEST: &str = "book";
const REPO_LINK: &str = "https://github.com/pluto/ronkathon/blob/main/";
const SHOW_CHANGES: bool = false;

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
  let rs_links = Regex::new(r"(?<t>\[.*\])\([/]?(?<l>.*\.rs)\)").unwrap();

  for src in &readmes {
    println!("Working on: {}", src.display());
    let mut src_parent = src.parent().unwrap().to_str().unwrap().to_owned();
    if !src_parent.is_empty() {
      src_parent.push('/');
    }

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
      let after1 = readme_re.replace_all(&before, "index.md");
      if before != after1 && SHOW_CHANGES {
        println!("1. {before} -> {after1}");
      }
      let after2 = rs_links.replace_all(&after1, format!("$t({}{}$l)", REPO_LINK, src_parent));
      if after1 != after2 && SHOW_CHANGES {
        println!("2. {after1} -> {after2}");
      }
      dest_file.write_all(after2.as_bytes())?;
      dest_file.write_all(b"\n")?;
    }
  }

  println!("Copying SUMMARY.md to {DEST}/SUMMARY.md");
  fs::copy("SUMMARY.md", "book/SUMMARY.md")?;

  println!("Done!");

  Ok(())
}
