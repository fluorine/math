# Reproducing the curated finite results

Use Python 3.11 or later (`hashlib.file_digest` is required). No external
Python package, SAT solver, browser connection, or network access is needed.
The checkers regenerate literal geometry and replay fixed finite objects;
they do not search for strategies.

From `board_size/`, list the thirteen cases and run one with a fresh path:

```sh
python3.12 -B reproduce.py --list
python3.12 -B reproduce.py browser_twentythird_maker01 --output /tmp/rgap-obstruction-replay.json
```

The mathematical output goes to the requested path. Its provenance and exact
comparison go to the same filename followed by `.publication.json`. An
existing output is refused so that failures and old evidence are preserved.

## What is unchanged

[inputs.json](inputs.json) records every included code/data file and its
SHA256. Mathematical checker and helper bytes, physical states, witnesses,
policies, controls, and accepted historical JSON are unchanged. Imports are
restricted by the frozen reviewed code, and the runner checks the whole
compact input closure before invoking it.

The historical checkers pin raw browser captures as provenance. Those captures
are not suitable publication inputs. For each affected path, the manifest
records its historical hash, the sanitized mathematical-text hash, and the
specific extraction. The runner imports the unchanged checker and substitutes
only those explicitly listed text values in that checker's `PINS` dictionary.
It does not change a mathematical routine or a helper's historical bindings.
Run through `reproduce.py`; invoking a historical checker directly will
correctly reject the intentionally changed text provenance.

## What is compared

The entire new JSON result is compared recursively with the accepted
historical report. Dictionary keys, list order and length, all states,
coverage ledgers, witnesses, branch counts, status and scope flags must agree.
The only permitted differences are:

1. `input_sha256`, which must equal precisely the original mapping with the
   listed sanitized-text substitutions, and no others.
2. The explicitly named top-level execution fields for that case: timestamps,
   process CPU and elapsed wall time. The manifest lists these fields; the
   runner validates their types and does not suppress nested differences.

There is no blanket provenance filter. A changed code/data hash or a changed
mathematical field prevents acceptance. The one negative control in
[wrapper-negative-control.json](wrapper-negative-control.json) changed a code
hash in a temporary manifest and verified rejection before any audit ran.

## Publication replay

The [accepted summary](accepted.json) binds all thirteen distinct publication
reports and comparison receipts. They passed once, using 2.518 process CPU
seconds in total, 5.747 guarded wall seconds and at most 57,638,912 bytes of
sampled process-family memory. Each ran as one nice-19 Python child under a
15-CPU-second, 60-wall-second, 150-MiB verification guard; no pressure event
occurred. The negative control used the smaller 5/30/100 limits.

The execution directory preserves the new guards, logs and exact launch
bindings. Historical reports elsewhere in this package remain separate and
retain their historical source/input hashes. An accepted publication replay
means the finite result was reproduced from the sanitized public inputs; it
does not upgrade a finite certificate or experimental observation into a Lean
kernel theorem.
