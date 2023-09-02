//! This tool is meant to be used by `cargo` when passed as part of
//! `RUSTC_WRAPPER`.
//!
//! It will execute `rustc` regularly, and immediately after, if the crate
//! being built is relevant to the linter, `redpen` will be executed with
//! slightly modified arguments and its output presented to the user.

use std::env::args;
use std::io::{self, Write};
use std::process::Command;

fn main() {
    let mut x = args();
    let _ = x.find(|a| a == "--crate-name");
    let crate_name = x.next();
    let args = args().collect::<Vec<String>>();

    let output = Command::new(&args[1])
        .args(&args[2..])
        .output()
        .expect("failed to execute process");
    if !crate_name.as_deref().map_or(false, |name| {
        !["___", "build_script_build", "redpen"].contains(&name)
    }) {
        io::stdout().write_all(&output.stdout).unwrap();
        io::stderr().write_all(&output.stderr).unwrap();
    } else if !output.status.success() {
        io::stdout().write_all(&output.stdout).unwrap();
        io::stderr().write_all(&output.stderr).unwrap();
    }

    let Some(crate_name) = crate_name else {
        return;
    };
    if !["___", "build_script_build", "redpen"].contains(&crate_name.as_str()) {
        let mut args = args.clone();
        args.remove(0);
        args.remove(0);
        args.insert(0, "-Zcrate-attr=feature(register_tool)".to_string());
        args.insert(0, "-Zcrate-attr=register_tool(redpen)".to_string());
        let mut iter = args.into_iter().peekable();
        let mut args = vec![];
        while let Some(arg) = iter.next() {
            if let Some(next) = iter.peek() {
                if next.starts_with("redpen") {
                    iter.next();
                    continue;
                }
            }
            args.push(arg);
        }
        args.push("--cfg".to_string());
        args.push("redpen".to_string());

        let output = Command::new("rustc_redpen")
            .args(&args[..])
            .output()
            .expect("failed to execute process");
        io::stdout().write_all(&output.stdout).unwrap();
        io::stderr().write_all(&output.stderr).unwrap();
    }
}
