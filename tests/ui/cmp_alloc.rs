#![deny(redpen::infallible_allocation)]

fn main() {
    let s = Some("hi".to_string());
    assert!(s == Some("hi".to_string()));
    assert!(s.as_deref() == Some("hi"));
}
