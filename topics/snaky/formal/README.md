# Lean certificates and game theorems

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

A second, independent rebuild on 15 October 2026 used the official
`lean-4.34.1-linux.tar.zst` release, which reports the same commit, on
Linux x86_64. It ran the identical per-module `lean -j 1 -M 4096` commands,
four modules at a time in dependency order. All 1,182 modules of the
`Snaky.Audit` closure compiled. The theorem types and axiom lists were
identical to those recorded in `kernel-audit.json`.

The local runtime was obtained from the
[official Lean 4.34.1 release](https://github.com/leanprover/lean4/releases/tag/v4.34.1):
`lean-4.34.1-darwin_aarch64.tar.zst`, SHA-256
`65f22a4f047738ec742667b3247e836a86ebf06eabc12655c3dee00637e37866`.
It reports commit `5045d0056413266e57c625dcd7c365b10e377c52`.
The archive and extracted runtime remain in the repository's ignored research
cache, not in this artifact. Use the matching official asset for another host.

## Separate 15×15 theorem within 24 Maker claims

`Snaky/Result15x15_24.lean` states the bounded finite-board theorem:

```lean
Snaky.snaky_wins_15x15_in_24 :
  Snaky.BlackWinsIn (Snaky.placements 15 15 Snaky.snaky) (15 * 15) 24 [] []
```

The complete target and its axiom audit passed on 15 October 2026. Its only
axioms are `propext`, `Classical.choice` and `Quot.sound`; no placeholders,
custom axioms or native-decision shortcuts occur. All 4,050 dependency modules
have successful compiler records. The final resume compiled 240 modules and
reused 3,810 after source/compiler/dependency-digest checks. See the
[kernel audit](kernel-audit-15x15-24.json),
[complete build evidence](../verification/snaky15x15-24-lean-build.json), and
[exact theorem/axiom output](../verification/snaky15x15-24-axioms.txt).

To reproduce:

```sh
python3 topics/snaky/formal/build.py --lean /absolute/path/to/lean \
  --generated-name Gen15x15_24 --target Snaky.AxiomAudit15x15_24 \
  --certificate topics/snaky/certificate/snaky15x15-24.cards.txt \
  --units 200000 --max-cards 15 --max-cells 2 --data-cards 125 \
  --memory-mb 2048 --module-seconds 180
```

This uses one Lean thread, a 2,048 MB compiler memory cap and a 180-second
per-module timeout. It generates 70 data files and 3,971 proof files, plus
`Tree.lean` and `All.lean`. The smaller data groups use
`tools/cards2lean_sized.py`, which changes only the pinned generator's
`PER_FILE` grouping constant. The certificate and card rules are unchanged.

The build report binds the certificate, generator, adapter and generated
sources by SHA-256, and checks that the inputs did not change during the run.
Unchanged checked modules can be reused after interruption. The result is
separate from the nineteen-move targets; their default build arguments remain
unchanged. The historical nineteen-move audit records the earlier builder
hash; this shared builder adds only the documented generation options and
input-hash reporting. The nineteen-move theorem and soundness sources are
unchanged. See [the result note](../RESULT-15X15-24.md) for independent checks
and the soundness argument.

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

## Board-size closeout

The separate [board-size research package](../board_size/README.md) concerns
conditional positions and local constructions on 10×10 and 14×14. Neither
empty-board objective was solved. The existing 19- and 24-move targets above
are unchanged.

The new proof package includes its literal data and every generated Lean
module. Rebuild the committed sources with Lean 4.34.1:

```sh
python3 topics/snaky/formal/build.py --lean /absolute/path/to/lean \
  --no-generate --target Snaky.BoardSizeAudit \
  --memory-mb 4096 --module-seconds 180
```

This runs one compiler thread at a time and needs no mathlib, solver, browser
session or research cache. `--no-generate` is intentional: the published
sources are the canonical proof input. The shared builder's certificate hash
field still records its default 19-move input for compatibility; that field
is not the data binding for the board-size theorems. The separate
[kernel audit](kernel-audit-board-size.json) records the exact new source
closure and theorem audit.

Every finite data assertion uses the Lean kernel. The card and defensive
soundness arguments connect the finite objects to the ordinary game, including
fresh moves, immediate completion and the last legal Maker claim. The selected
C30 attack and the e1 replacement lemma have narrower statements: C30 concerns
its displayed selected guards, and e1 assumes explicit compatibility conditions.
Neither is an unrestricted physical game outcome.

The final audit imports all delivered theorem roots and prints their types and
axioms. Previously checked, byte-identical common game/card modules were reused
after source, compiler, recursive import and object checks; the new modules
were checked locally during closeout. A clean invocation of the command above
rechecks the common modules too. Verification evidence describes which work
was fresh and which was reused; cached objects are not part of the published
proof source.

The conditional opening source generator can be run separately with Python
3.11 or newer. The compact deck and closure map are included; the large
historical search libraries are not needed:

```sh
python3.12 topics/snaky/formal/tools/maker_opening_data.py \
  --from-extracted --output-dir /tmp/snaky-opening-regenerated
```

The [regeneration receipt](Snaky/GenMakerOpening/regeneration.json) records a
byte-for-byte comparison of all 1,761 generated Lean files. The closure map's
original generator hash is historical; the receipt binds the current generator.

The release also requires a [fresh kernel replay](kernel-fresh-board-size.json)
of the complete aggregate. This uses the shipped Lean 4.34.1 `leanchecker`
with `--fresh`: it replays safe declarations into an empty kernel environment
and checks the induced constructors and recursors. It is the Lean kernel,
not a separate verifier implementation. After the source build above, from
the repository root:

```sh
PATH="/absolute/path/to/lean-toolchain/bin:$PATH" \
LEAN_PATH="$PWD/topics/snaky/formal/.build/lib" \
  /absolute/path/to/lean-toolchain/bin/leanchecker --fresh --verbose Snaky.BoardSizeAudit
```

Some early opening receipts recorded dependency source hashes without
per-compilation imported-object hashes. The release therefore binds the full
current source/object closure and requires this fresh replay, in addition to
the source compilation and theorem/axiom audit. Historical local telemetry
hashes in family manifests are provenance; rebuilding the committed sources
does not depend on those private cache files.
Source hashes pin the portable proof inputs. Object hashes identify the
recorded local build and can differ across compiler platforms or build paths.
