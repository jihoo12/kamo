#!/usr/bin/env python3
"""Bounded public-CLI probes. Run from any directory after cargo build --release."""
import json
import resource
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BIN = ROOT / 'target/release/kamo'
# Prevent core dumps if the historical stack-overflow regression returns.
resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
results = []

def run(path, command, name=None, reference=False):
    args = [str(ROOT / 'scripts/with-limits.sh'), str(BIN), command, str(path)]
    if name:
        args.append(name)
    if reference:
        args.append('--reference')
    return subprocess.run(args, cwd=ROOT, text=True, capture_output=True, timeout=35)

with tempfile.TemporaryDirectory(prefix='kamo-public-audit-') as directory:
    directory = Path(directory)
    invalid = {
        'false-path': '(def bad (Path i Bool true false) (path i true))',
        'universe-cycle': '(def bad (U 0) (U 0))',
        'false-cover': '(def bad (Path i Bool true true) (path i (system Bool (((or (= i 0) (= i 1)) true)))))',
        'bad-cap': '(def bad Bool (com i Bool 0 1 true ((top false))))',
        'bad-overlap': '(def bad Bool (system Bool ((top true) (top false))))',
        'self-reference': '(def bad Bool bad)',
        'bad-equivalence': '(def bad (U 0) (Glue Bool ((top Bool true))))',
        'diagonal-overlap': '(def bad (Path i (Path j Bool true true) (path j true) (path j true)) (path i (path j (com k Bool 0 1 true (((= i j) true) ((= j 0) false))))))',
    }
    for name, source in invalid.items():
        path = directory / f'{name}.kamo'
        path.write_text(source)
        for reference in [False, True]:
            out = run(path, 'check', reference=reference)
            assert out.returncode == 1, (name, reference, out.returncode, out.stderr)
            results.append({'case':name, 'reference':reference, 'result':'rejected', 'diagnostic':out.stderr.strip()})
    valid = {
        'open-coe': ('(Pi p (Path i (U 0) Bool Bool) (Pi x Bool Bool))', '(lam p (lam x (coe i (at p i) 0 1 x)))'),
        'open-pair': ('(Pi p (Path i (U 0) Bool Bool) (Pi x Bool (Sigma b Bool Bool)))', '(lam p (lam x (coe i (Sigma b (at p i) (at p i)) 0 1 (pair x x))))'),
        'open-function': ('(Pi p (Path i (U 0) Bool Bool) (Pi f (Pi x Bool Bool) (Pi x Bool Bool)))', '(lam p (lam f (coe i (Pi x (at p i) (at p i)) 0 1 f)))'),
        'restricted-computed-glue': ('(Path i Bool true true)', '(path i (unglue (coe k (U 0) 0 i Bool) (glue (coe k (U 0) 0 i Bool) true (((= i 0) true)))))'),
    }
    for name, (ty, body) in valid.items():
        path = directory / f'{name}.kamo'
        source = f'(def probe {ty} {body})\n'
        path.write_text(source)
        forms = []
        for reference in [False, True]:
            out = run(path, 'normalize', 'probe', reference)
            assert out.returncode == 0, (name, reference, out.stderr)
            normal = out.stdout.strip()
            forms.append(normal)
            roundtrip = directory / 'roundtrip.kamo'
            roundtrip.write_text(source + f'(def quoted {ty} {normal})\n' + f'(def agreement (Path i {ty} probe quoted) (path i probe))\n')
            checked = run(roundtrip, 'check', reference=reference)
            assert checked.returncode == 0, (name, reference, checked.stderr)
            results.append({'case':name, 'reference':reference, 'result':'normalized, rechecked, and definitionally equal', 'normal':normal})
        assert forms[0] == forms[1], name
    deep = directory / 'deep.kamo'
    deep.write_text('(def n0 Nat zero)\n' + ''.join(f'(def n{i} Nat (suc n{i-1}))\n' for i in range(1,30001)))
    checked = run(deep, 'check')
    assert checked.returncode == 0, checked.stderr
    out = run(deep, 'normalize', 'n30000')
    assert out.returncode == 0, (out.returncode, out.stderr)
    assert out.stdout.strip() == '(suc ' * 30000 + 'zero' + ')' * 30000
    results.append({'case':'deep-natural', 'source_bytes':deep.stat().st_size, 'declarations':30001, 'check':'accepted', 'normalization_exit':out.returncode, 'stderr':out.stderr.strip()})
print(json.dumps(results, indent=2))
