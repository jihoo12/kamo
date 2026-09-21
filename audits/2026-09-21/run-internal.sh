#!/usr/bin/env bash
# Tests a disposable source copy; never modifies the kernel. The conversion
# assertions failed on the audited revision and must pass after remediation.
set -euo pipefail
cd "$(dirname "$0")/../.."
work=$(mktemp -d /tmp/kamo-audit.XXXXXX)
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/src" "$work/examples"
cp src/*.rs "$work/src/"
cp examples/prelude.kamo "$work/examples/"
cat audits/2026-09-21/substitution_tests.rs >> "$work/src/eval.rs"
cat audits/2026-09-21/face_tests.rs >> "$work/src/face.rs"
rustc --edition=2024 --test "$work/src/lib.rs" -o "$work/test"
scripts/with-limits.sh "$work/test" audit_ --nocapture --test-threads=1
