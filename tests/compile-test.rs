#![feature(lazy_cell)]

extern crate compiletest_rs as compiletest;

use std::env;
use std::path::PathBuf;
use std::sync::LazyLock;

static PROFILE_PATH: LazyLock<PathBuf> = LazyLock::new(|| {
    let current_exe_path = env::current_exe().unwrap();
    let deps_path = current_exe_path.parent().unwrap();
    let profile_path = deps_path.parent().unwrap();
    profile_path.into()
});

fn run_ui_tests(bless: bool) {
    let mut config = compiletest::Config {
        bless,
        edition: Some("2021".into()),
        mode: compiletest::common::Mode::Ui,
        ..Default::default()
    };

    config.target_rustcflags = Some(format!(
        "-Zcrate-attr=feature(register_tool) -Zcrate-attr=register_tool(redpen)"
    ));

    config.src_base = "tests/ui".into();
    config.build_base = PROFILE_PATH.join("test/ui");
    config.rustc_path = PROFILE_PATH.join("rustc_redpen");
    config.link_deps(); // Populate config.target_rustcflags with dependencies on the path

    compiletest::run_tests(&config);
}

#[test]
fn compile_test() {
    let bless = env::var("BLESS").map_or(false, |x| !x.trim().is_empty());
    run_ui_tests(bless);
}
