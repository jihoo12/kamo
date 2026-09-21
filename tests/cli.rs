use std::process::Command;

#[test]
fn checks_and_normalizes_from_the_cli() {
    let check = Command::new(env!("CARGO_BIN_EXE_kamo"))
        .args(["check", "examples/univalence.kamo"])
        .output()
        .unwrap();
    assert!(
        check.status.success(),
        "{}",
        String::from_utf8_lossy(&check.stderr)
    );
    assert!(String::from_utf8_lossy(&check.stdout).contains("checked 37 declarations"));
    let output = Command::new(env!("CARGO_BIN_EXE_kamo"))
        .args([
            "normalize",
            "examples/univalence.kamo",
            "neg-true",
            "--stats",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "false");
    assert!(String::from_utf8_lossy(&output.stderr).contains("arena_bytes"));
}

#[test]
fn failures_have_nonzero_status() {
    for args in [
        vec!["normalize", "examples/core.kamo", "missing"],
        vec!["check", "examples/core.kamo", "--max-nodes", "1"],
        vec!["unknown-command"],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_kamo"))
            .args(args)
            .output()
            .unwrap();
        assert!(!output.status.success());
        assert!(!output.stderr.is_empty());
    }
}
