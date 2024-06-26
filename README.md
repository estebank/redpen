# Red Pen ️❌🖊

`redpen` is a linter for Rust code.

## Goals

The aim of this tool is to:

* have its own custom sets of lints independent of clippy to allow for different defaults
* work as a test bed for internal `rustc` API stabilization
* act as a buffer between lints written for this tool and that internal API by providing its own API for compiler internals so that changing `rustc` API internals don't require regularly rewriting lints (this work has not yet been started)
* be quick to compile as part of CI so that projects can write project specific lints

## Implemented lints

Currently, only two lints have been written

 - a simple lint that operates as a "negative trait check", that complains if a type parameter of an annotated type is used with a specific type
 - a much more useful assertion that the annotated fn will not transitively call panic

## Meaning of the name

The tool is named after the writing instrument a teacher would use to mark mistakes in your paper. [`rustc` is a strict teacher][teacher]. `redpen` is a *very* strict teacher.

[teacher]: https://twitter.com/ekuber/status/1438178928984829959

## Installation and usage

There are two ways of using this tool. If you are only interested in using existing lints, you can install through `cargo` with `cargo +nightly-2024-05-06 install redpen-linter`. After that you can invoke `redpen` as if you were invoking `cargo check`. You must ensure that the appropriate Rust 1.72 compiler is installed with `rustup toolchain add nightly-2024-05-06`, as `redpen` is tightly coupled with a specific compiler version's internal APIs. Additionally, you must also add the following to your `Cargo.toml` in the `[dependencies]` section:

```
[dependencies]
cargo-redpen-shim = { version = "0.1", package = "redpen" }
```

This is necessary so that when running regular `cargo` commands, like `cargo build`, the custom linting annotations will be picked up as valid item attributes and not fail your build.

If you want to keep your own set of lints, then you'll have to keep your own working copy of the different `redpen` components.

Clone this repository and run `cargo install`:

```console
export LD_LIBRARY_PATH=$(rustup run nightly-2024-05-06 bash -c "echo \$LD_LIBRARY_PATH")
git clone https://github.com/estebank/redpen.git
cd redpen
cargo install --path .
```

Note that `redpen` is pinned to a Rust version so it is likely that running `cargo install --git` will not work as it will not use the `rust-toolchain` file in the repository.

If you're adding new lints, you will also want to provide your own `redpen` proc-macro crate.

## What it looks like

Given a `src/main.rs` with the following contents:

```rust
#[redpen::disallow(T = "Pineapple")]
struct Pizza<T>(T);

struct Pineapple;

#[allow(dead_code)]
type Alias = Pizza<Pineapple>;

impl Pineapple {
    fn foo(&self) {
        panic!("foo");
    }
}

#[redpen::dont_panic]
fn bar() {
    Pineapple.foo();
    let mut v = vec![1];
    v.swap_remove(0);
    v[1];
    panic!("asdf");
}

fn main() {
    bar();
    let _ = Pizza(Pineapple);
}
```

Executing `redpen` will produce the following output:

```
$ redpen
   Compiling pizza v0.1.0 (/home/gh-estebank/pizza)
error: `bar` can panic
  --> src/main.rs:16:1
   |
15 | #[redpen::dont_panic]
   | --------------------- the function can't panic due to this annotation
16 | fn bar() {
   | ^^^^^^^^ this function can panic
17 |     Pineapple.foo();
   |               --- panic can occur here
18 |     let mut v = vec![1];
19 |     v.swap_remove(0);
   |       ----------- panic can occur here
20 |     v[1];
   |     ---- panic can occur here
21 |     panic!("asdf");
   |     -------------- panic can occur here
   |
   = note: `#[deny(redpen::dont_panic)]` on by default

error: type parameter `T` in `Pizza` can't be `Pineapple`
 --> src/main.rs:7:20
  |
7 | type Alias = Pizza<Pineapple>;
  |                    ^^^^^^^^^
  |
  = note: `#[deny(redpen::disallow)]` on by default

error: type parameter `T` in `Pizza` can't be `Pineapple`
  --> src/main.rs:26:13
   |
26 |     let _ = Pizza(Pineapple);
   |             ^^^^^^^^^^^^^^^^ this expression is of type `Pizza<Pineapple>`

    Finished dev [unoptimized + debuginfo] target(s) in 0.02s
```

## How it works

This linter is implemented as a `rustc_driver`, effectively a different entry point to the regular `rustc` implementation. It links against the pre-built `rustc_*` components, so you're only compiling a very small amount of code, keeping its builds quite fast.

`redpen_wrapper` is a very small CLI tool that is meant to act as a passthrough between `cargo` and `rustc`. It is invoked through `RUST_WRAPPER=redpen_wrapper cargo build`. This allows us to use `rustc` to build a given crate, and only once this is done, execute `redpen` to execute the lints and collect metadata necessary for cross-crate analysis (like the `panic!()` reachability lint).

`cargo-redpen` is a small CLI that invokes `cargo build` with the appropriate environement variables. It executes:

```console
export LD_LIBRARY_PATH=$(rustup run nightly-2024-05-06 bash -c "echo \$LD_LIBRARY_PATH")

RUSTC_WRAPPER=$PATH_TO/redpen_wrapper \
RUSTC_BOOTSTRAP=1 \
cargo +nightly-2024-05-06 build \
-Zbuild-std \
--target x86_64-unknown-linux-gnu # haven't tried in other platforms, experiment replacing this for your case
```

## Ancestry notice

This linter was initially based of off [the Rust-on-Linux linter klint][klint], which in turn leverages the `rustc` codebase.

[klint]: https://github.com/Rust-for-Linux/klint
