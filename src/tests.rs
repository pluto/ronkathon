use rstest::{fixture, rstest};

// rstest provides features to take common context into tests, and set up small cases testing
#[derive(Clone, Debug, Eq, PartialEq)]
struct Wb {
  count: usize,
}

// context setup function to be implicitly called by `wb`
#[fixture]
fn count() -> usize { return 0usize; }

// context setup function to be implicitly called by `test_wb`
#[fixture]
fn wb(count: usize) -> Wb {
  let _ = env_logger::builder().filter_level(log::LevelFilter::Debug).is_test(true).try_init();
  Wb { count }
}

#[rstest]
fn test_wb(wb: Wb) {
  log::info!("wb: {wb:?}");
  let Wb { count } = wb;
}
