# Red Pen 🖊️

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

There are two ways of using this tool. If you are only interested in using existing lints, you can install through `cargo` with `cargo install cargo-redpen`. You must ensure that the appropriate Rust 1.72 compiler is installed with `rustup toolchain add 1.72.0`, as `redpen` is tightly coupled with a specific compiler version's internal APIs. Additionally, you must also add the following to your `Cargo.toml` in the `[dependencies]` section:

```
[dependencies]
cargo-redpen-shim = { version = "0.1", package = "redpen" }
```

This is necessary so that when running regular `cargo` commands, like `cargo build`, the custom linting annotations will be picked up as valid item attributes and not fail your build.

If you want to keep your own set of lints, then you'll have to keep your own working copy of the different `redpen` components.

Clone this repository and run `cargo install`:

```console
export LD_LIBRARY_PATH=$(rustup run 1.72.0 bash -c "echo \$LD_LIBRARY_PATH")
git clone https://github.com/estebank/redpen.git
cd redpen
cargo install --path .
```

Note that `redpen` is pinned to a Rust version so it is likely that running `cargo install --git` will not work as it will not use the `rust-toolchain` file in the repository.

If you're adding new lints, you will also want to provide your own `redpen` proc-macro crate.

## How it works

This linter is implemented as a `rustc_driver`, effectively a different entry point to the regular `rustc` implementation. It links against the pre-built `rustc_*` components, so you're only compiling a very small amount of code, keeping its builds quite fast.

`redpen_wrapper` is a very small CLI tool that is meant to act as a passthrough between `cargo` and `rustc`. It is invoked through `RUST_WRAPPER=redpen_wrapper cargo build`. This allows us to use `rustc` to build a given crate, and only once this is done, execute `redpen` to execute the lints and collect metadata necessary for cross-crate analysis (like the `panic!()` reachability lint).

`cargo-redpen` is a small CLI that invokes `cargo build` with the appropriate environement variables. It executes:

```console
export LD_LIBRARY_PATH=$(rustup run 1.72.0 bash -c "echo \$LD_LIBRARY_PATH")

RUSTC_WRAPPER=$PATH_TO/redpen_wrapper \
RUSTC_BOOTSTRAP=1 \
cargo +1.72.0 build \
-Zbuild-std \
--target x86_64-unknown-linux-gnu # haven't tried in other platforms, experiment replacing this for your case
```

## Ancestry notice

This linter was initially based of off [the Rust-on-Linux linter klint][klint], which in turn leverages the `rustc` codebase.

[klint]: https://github.com/Rust-for-Linux/klint
