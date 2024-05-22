// #![feature(print_internals)]
use std::fs::File;
use std::io::{self, Write};

#[redpen::assume_bad("blocking_async")]
fn interesting() {}
fn uninteresting() {}

#[redpen::assume_ok("blocking_async")]
fn can_block_ignored() {
    interesting();
}

fn transitive() {
    interesting();
}

// Triggers here because it calls a function that is transitively blocking.
async fn bar() {
    transitive();
}

// Doesn't trigger here because `uninteresting` isn't known to be blocking.
async fn baz() {
    uninteresting();
}

// Doesn't trigger here because `can_block_ignored` is annotated as non-blocking.
async fn bal() {
    can_block_ignored();
}

async fn blocks_on_sleep() {
    std::thread::sleep(std::time::Duration::from_millis(1));
}

// FIXME: this should trigger
async fn asdf() -> io::Result<()> {
    let mut stdout = io::stdout().lock();
    stdout.write_all(b"hello world")?;
    Ok(())
}
// Need to fix the handling of closures in the collector to avoid ICE.
// async fn foo(closure: impl Fn()) {

// Triggers here, and points at multiple instances of the same await, so it also shows why `bar` is
// blocking.
async fn indirect() {
    bar().await;
    bar().await;
    // println!("Hello, stdout!");
    // interesting();
    // closure();
    // ::std::io::_print(format_args!("Hello, stdout!\n"));
    // let mut file = File::create("foo.txt").unwrap();
    // file.write_all(b"Hello, world!").unwrap();

}

// Triggers here, but it doesn't climb the causal chain because there are more than one reasons
// this function is blocking.
async fn multiple() {
    bar().await;
    blocks_on_sleep().await;
    std::thread::sleep(std::time::Duration::from_millis(1));
    // println!("Hello, stdout!");
    // interesting();
    // closure();
    // ::std::io::_print(format_args!("Hello, stdout!\n"));
    // let mut file = File::create("foo.txt").unwrap();
    // file.write_all(b"Hello, world!").unwrap();

}

// Doesn't trigger here because it is not async
fn bat() {
    interesting();
}

fn main() {
    // let _ = foo(|| { transitive(); });
}
