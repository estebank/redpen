#![deny(redpen::dont_panic_in_drop)]
struct S;

impl Drop for S {
    fn drop(&mut self) {
        panic!()
    }
}

fn main() {}