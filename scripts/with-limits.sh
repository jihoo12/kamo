#!/usr/bin/env bash
# Linux/Bash development runner: cap virtual address space and wall-clock time.
set -euo pipefail
ulimit -v "${KAMO_MEMORY_KIB:-524288}"
exec timeout --signal=TERM --kill-after=2s "${KAMO_TIMEOUT:-30s}" "$@"
