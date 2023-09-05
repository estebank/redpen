#![allow(redpen::infallible_allocation)]
#![deny(redpen::dont_panic)]

fn main() {
    let mut x: Vec<&str> = vec![];
    x.push("");
    let _ = x[1];
}
