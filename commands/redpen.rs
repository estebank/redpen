//! This tool is meant to be used as a `cargo` plugin, invoked as
//! `cargo redpen`.
//!
//! It will set-up the necessary environment variables and execute `cargo`
//! telling it to use `redpen_wrapper`, which in turn will execute the
//! `rustc_redpen` linter executable.

use std::env::set_var;
use std::io::{self, BufRead, BufReader, Write};
use std::process::{Command, Stdio};

enum Stream {
    Out,
    Err,
}

fn main() {
    // We tell `cargo` to use our wrapper instead of `rustc` directly.
    set_var("RUSTC_WRAPPER", "redpen_wrapper");
    // We need cargo to let us build std owrselves.
    set_var("RUSTC_BOOTSTRAP", "1");
    // We need to access the existing `rustc` libraries to link to during runtime.
    set_var(
        "LD_LIBRARY_PATH",
        "/home/gh-estebank/.rustup/toolchains/1.72.0-x86_64-unknown-linux-gnu/lib",
    ); // FIXME get from user's environment
    let mut cmd = Command::new("cargo")
        .args([
            "+1.72.0",
            "build",
            "-Zbuild-std",
            "--target",
            "x86_64-unknown-linux-gnu", // FIXME get from the user's environment
            "--color=always",           // FIXME check isatty
        ])
        .stdout(Stdio::piped())
        .spawn()
        .expect("failed to execute process");
    let stdout = cmd.stdout.as_mut().unwrap();
    let stdout_reader = BufReader::new(stdout);
    let stdout_lines = stdout_reader.lines().map(|l| (Stream::Out, l));

    let stderr_lines = if let Some(stderr) = cmd.stderr.as_mut() {
        let stderr_reader = BufReader::new(stderr);
        Box::new(stderr_reader.lines().map(|l| (Stream::Err, l)))
            as Box<dyn std::iter::Iterator<Item = (Stream, Result<String, _>)>>
    } else {
        Box::new([].into_iter())
    };

    for (stream, line) in stdout_lines.chain(stderr_lines) {
        let Ok(line) = line else {
            continue;
        };
        match stream {
            Stream::Out => io::stdout().write_all(line.as_bytes()).unwrap(),
            Stream::Err => io::stderr().write_all(line.as_bytes()).unwrap(),
        }
    }
    cmd.wait().unwrap();
}
