struct BooleanArrayIter {
    current: Vec<bool>,
    done: bool,
}

impl Iterator for BooleanArrayIter {
    type Item = Vec<bool>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        let result = self.current.clone();

        // Generate next array
        for i in 0..self.current.len() {
            if self.current[i] {
                self.current[i] = false;
            } else {
                self.current[i] = true;
                return Some(result);
            }
        }

        // If we've reached here, we've generated all arrays
        self.done = true;
        Some(result)
    }
}

pub fn get_all_possible_boolean_values(length: usize) -> impl Iterator<Item = Vec<bool>> {
    BooleanArrayIter {
        current: vec![false; length],
        done: false,
    }
}