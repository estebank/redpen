#![allow(redpen::infallible_allocation)]
#![deny(redpen::panics)]

fn main() {
    let mut x: Vec<&str> = vec![];
    x.push("");
    let _ = x[1];
    x[1] = "";
}
