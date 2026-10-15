# Lean certificate and infinite-board theorem

The formal target is the actual infinite-board game:

```lean
Snaky.snaky_wins_plane_in_19 : Snaky.PlaneBlackWinsIn 19 [] []
```

`Snaky/Plane.lean` defines cells as `Int × Int`, requires every claim to be
fresh, quantifies over every legal integer-pair Breaker reply, and counts Maker
claims including the winning claim. Its soundness proof handles replies
outside finite support directly. `Result19.lean` also proves the corresponding
finite-board statement:

```lean
Snaky.snaky_wins_17x17_in_19 :
  Snaky.BlackWinsIn (Snaky.placements 17 17 Snaky.snaky) (17 * 17) 19 [] []
```

## Build

Use Lean **4.34.1**. From the repository root:

```sh
python3 topics/snaky/formal/build.py --lean /absolute/path/to/lean --target Snaky.Audit
```

If the pinned compiler is already on PATH, omit `--lean`. The script generates
Lean card data from `../certificate/snaky19.cards.txt` and compiles the exact
dependency closure serially, with one computational thread and a 4,096 MB
memory cap per process. Each module has a 180-second wall limit. Generated
proof chunks, compiled files and resumable hashes live in ignored local paths.
An interrupted run resumes unchanged modules; a source or dependency change
invalidates its cached result. No mathlib or external Lean packages are needed.

`Snaky.Audit` prints both exact theorem types and their axioms. All data checks
use `decide +kernel`; no `native_decide`, proof placeholders or custom axioms
are part of this development. The complete build succeeded on 15 October 2026.
Both final theorems report exactly `propext`, `Classical.choice` and `Quot.sound`
as their axioms. Exact output and build metrics are in `kernel-audit.json`.
The result target has 1,181 modules in its dependency closure; the main serial
pass took 1,832 seconds and used at most 2.20 GiB resident memory in a child
process. Six base modules were already checked and reused by that pass.

The local runtime was obtained from the
[official Lean 4.34.1 release](https://github.com/leanprover/lean4/releases/tag/v4.34.1):
`lean-4.34.1-darwin_aarch64.tar.zst`, SHA-256
`65f22a4f047738ec742667b3247e836a86ebf06eabc12655c3dee00637e37866`.
It reports commit `5045d0056413266e57c625dcd7c365b10e377c52`.
The archive and extracted runtime remain in the repository's ignored research
cache, not in this artifact. Use the matching official asset for another host.

## Provenance and trust boundary

The following files are copied unchanged from
[gotrevor/snaky-15x15 at b18ed32473a6a22ebfdda98da62d61b8b1590c1e](https://github.com/gotrevor/snaky-15x15/tree/b18ed32473a6a22ebfdda98da62d61b8b1590c1e):

- `Snaky/Game.lean`, `Cards.lean`, `Controls.lean`, `Bounded.lean`, `CardsSound.lean`;
- `CardCheck.lean`, `lean-toolchain`, and `tools/cards2lean.py`.

The upstream Apache-2.0 license is retained in `../reference/gotrevor-LICENSE`.
`Plane.lean`, `Result19.lean`, `Audit.lean` and `build.py` are this project's new
work. The generator is untrusted: each resulting card obligation is reduced
by the Lean kernel, and the imported soundness theorem connects those exact
checks to legal game play. A new direct plane soundness theorem supplies the
infinite-board conclusion; no unformalized finite-to-infinite transfer is hidden
in the stated Lean theorem.
