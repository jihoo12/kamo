#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
ulimit -c 0
output_dir=audits/2026-09-22
for size in 4 12 24; do
    case "$size" in
        4) nodes=4000000; fuel=4000000; memory=2097152; bytes=16777216; tasks=250000 ;;
        12) nodes=12000000; fuel=40000000; memory=4194304; bytes=67108864; tasks=1000000 ;;
        24) nodes=24000000; fuel=100000000; memory=8388608; bytes=67108864; tasks=1000000 ;;
    esac
    status=0
    KAMO_MEMORY_KIB="$memory" scripts/with-limits.sh "${KAMO_TIME:-/usr/bin/time}" \
        -f 'elapsed=%e rss_KiB=%M exit=%x' target/release/kamo normalize \
        examples/univalence.kamo univalence --max-nodes "$nodes" --fuel "$fuel" \
        --max-output-bytes "$bytes" --max-quote-tasks "$tasks" \
        > "$output_dir/univalence-${size}m.out" 2> "$output_dir/univalence-${size}m.log" || status=$?
    echo "${size}m: exit=$status"
    cat "$output_dir/univalence-${size}m.log"
done
