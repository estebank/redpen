#![allow(redpen::infallible_allocation)]
// #![deny(redpen::dont_allocate)]
// #![deny(redpen::dont_panic, redpen::dont_allocate, redpen::dont_leak, redpen::from_raw_parts)]

struct X;
struct Y;

// unsafe fn bar() {}
// fn foo() {
//     let x = &42;
//     // std::process::exit(0);
//     // let x = unsafe { std::slice::from_raw_parts(x as *const _, 1)};
//     unsafe { bar(); }
// }
fn main() {
    // // let Y = unsafe { std::mem::transmute(X) };
    // let _: i32 = unsafe { std::mem::transmute(0u32) };
    // foo();
    // // foo();
    // vec![1, 2, 3].len();
    // Box::leak(Box::new(1));
    // // vec![1].leak();
    // let mut x: Vec<&str> = vec![];
    // // x.push("");
    // // let _ = x[1];
    // // x[1] = "";
    // std::mem::forget(x);
    // u32::checked_add(42, 42);
    // let _ = 3u16 + 23;
    // println!("");
    let mut x = std::io::stderr();
    let y = x.lock();
}
