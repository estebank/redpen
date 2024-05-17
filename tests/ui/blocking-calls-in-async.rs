// #![feature(print_internals)]
use std::fs::File;
use std::io::Write;

#[redpen::assume_bad("blocking_async")]
fn interesting() {}
fn uninteresting() {}

#[redpen::assume_ok("blocking_async")]
fn can_block_ignored() {
    println!("can't touch this");
}

fn transitive() {
    interesting();
}

async fn bar() {
    interesting();
}
async fn baz() {
    uninteresting();
}
async fn bal() {
    can_block_ignored();
}
// async fn foo(closure: impl Fn()) {
async fn foo() {
    bar().await;
    // baz().await;
    // println!("Hello, stdout!");
    // interesting();
    // closure();
    // ::std::io::_print(format_args!("Hello, stdout!\n"));
    // let mut file = File::create("foo.txt").unwrap();
    // file.write_all(b"Hello, world!").unwrap();

}
fn bat() {
    interesting();
}

fn main() {
    // let _ = foo(|| { transitive(); });
    let _ = foo();
    
    let _ = bat();
}
