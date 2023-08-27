#![allow(clippy::prevent_hash_map_iterations)]
use std::collections::HashMap;

fn main() {
    // test code goes here
    let map: HashMap<u32, u32> = HashMap::new();
    map.iter();
}
