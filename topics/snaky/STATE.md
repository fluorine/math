# Research state

Updated 2026-10-15. **The 19-move result is complete, independently verified,
fully checked by the Lean kernel, and reproduced byte for byte.** The proof
covers both the empty infinite square board and the empty 17×17 board.

The user authorized publication on 15 October 2026. This release contains only
the completed nineteen-move result from verified research commit `0a858c3`.
Further Snaky research remains on a separate local branch. The announcement
under `publication/X_POST.txt` is a draft, not a claim that it has been posted.

## Location and ownership

- Repository: `/Volumes/2tb/math`, original HEAD `7566886575317521d0b9510c7ef1198845ccec4f`.
- Isolated worktree: `/Volumes/2tb/math/.worktrees/snaky19-20261015-a`.
- Verified research branch: `research/snaky19-20261015-a` at `0a858c3`.
- Publication integration branch: `publication/snaky19-20261015`, based on the
  repository's current main branch and preserving the sensitivity contribution.
- Scope: `topics/snaky/`; other sessions have separate worktrees. Do not modify them.
- Root owns specifications, integration and result claims. Constructor owns
  `constructor/` and `MANUSCRIPT.md`; independent verifier owns `verification/`.
  Tactics worker wrote `formal/Snaky/Plane.lean` and `Result19.lean`. Root owns
  formal build infrastructure. Publication of this completed result is authorized;
  follow-on results remain separate and are not included in this release.

## Host and limits

Apple ARM64 Darwin 25.3.0, 8 logical CPUs, 16 GiB RAM. Initial disk availability
368 GiB on `/Volumes/2tb`. Swap already used about 4.65 GiB; other workloads include
compression and Python tasks. Start with one CPU-intensive experiment at a time,
at most two computational threads, and modest memory use. Do not run the upstream
15×15 tree checker (documented 20 GB RAM) under this resource envelope.

Tools observed: Git 2.50.1, gh 2.92.0, Apple clang 21.0.0, system Python 3.9.6;
Homebrew Python 3.12/3.14 available. Lean/lake initially absent from PATH. A local
Lean 4.34.1 ARM runtime was downloaded from the official release and its archive
SHA-256 checked: `65f22a4f047738ec742667b3247e836a86ebf06eabc12655c3dee00637e37866`.
Executable: `/Volumes/2tb/math/.research-cache/toolchains/lean-4.34.1-darwin_aarch64/bin/lean`.
Formal checks use one thread and a 4,096 MB Lean memory cap. No paid/cloud compute.

## Completed

- Read task brief and inspected host and clean initial repository.
- Cloned repository and created isolated worktree/unique research branch.
- Refreshed novelty audit before strategic search; see `NOVELTY.md`.
- Read exact 20-move Lean statement, card rules, shape and 15×15 result.
- Saved 764,733-byte baseline certificate with provenance, not as a new result.
- Independently checked all 1,738 baseline cards (36,625 inside response checks,
  1,732 outside classes); root height and longest hint dependency both 20.
- Independently checked the compact 15×15 set (8,671 cards, 139,698 inside
  responses, 8,665 outside classes); root height/dependency both 25. Vendored
  as an optional tactical library. No enormous tree checker used.
- Nineteen verifier controls passed, including malformed terminals, missing
  branches, incorrect heights, wrong symmetries and first-match lookup.
- Reconstructed 15,696 maximal labelled dependency routes through 59 critical
  cards. Full-history replay partitions them into 9,792 repeated Maker pivots,
  2,592 illegal repeated Breaker replies, 864 earlier wins and 2,448 legal
  20-move transcripts. This is about the fixed policy, not game optimality.
- Combined-catalog construction completed in 14.90 seconds on one thread,
  using full Maker history and safe region U minus actual Breaker history.
  It emitted 153 new cards, making 180 shortcut substitutions. Every shortcut
  reuses safe cells outside the current baseline template; 68 reuse forgotten
  Maker stones. No zero-cost-pivot step was needed in the successful run.
- Final `certificate/snaky19.cards.txt` is 1,365,722 bytes, 3,468 reachable cards,
  root 3467 with height 19, empty requirements and 249 support cells in [0,16]².
  SHA-256 `baf8774e1fc6eea60b1756437e8b3caae0ede5e001b10c0c3787aab51840782e`.
- Independent verifier accepted final certificate: 61,040 inside replies,
  3,456 outside classes. Thirty-one focused verification tests passed; final
  root-height reduction and missing-response corruptions correctly rejected.
- Adversarial semantic review found no gap in the direct plane soundness proof.
- Unchanged upstream Lean base modules and new direct infinite-board soundness
  module `Snaky.Plane` compiled with Lean 4.34.1, without proof placeholders.
- Full `Snaky.Result19` build succeeded: 1,181 modules in its dependency closure,
  1,175 newly compiled in the final pass and six previously checked base modules.
  The serial pass took 1,832 seconds; peak child RSS was 2,360,246,272 bytes.
- `Snaky.Audit` printed the exact finite and infinite 19-move theorem types.
  Both depend only on `propext`, `Classical.choice` and `Quot.sound`, with no
  placeholders, custom axioms or native decision procedure.
- Final `python3 topics/snaky/reproduce.py --reconstruct` exited successfully:
  all 31 tests passed, both certificate corruptions were rejected, and the
  reconstructed compact certificate was byte-for-byte identical. Construction
  took 13.66 seconds in this final reproduction.
- `formal/kernel-audit.json` records the completed evidence. `MANUSCRIPT.md`
  gives the mathematical proof, construction, explicit substitutions and credits.

## Final state

The requested 19-move target is achieved. No search or proof build is left
running. All delivered files are under `topics/snaky/` on the isolated research
branch. The 18-move question and optimality remain outside this completed result.

Ignored local build outputs and hashes remain under `formal/.build/`; generated
`Gen19` uses 1,165 proof modules with 400,000-unit / 5-response-cell chunks to
bound memory. They can be recreated with the documented build command.

Failed elementary approach: retaining stones and skipping already-owned pivots
alone does not establish 19, since genuine 20-move baseline transcripts remain.
This is not a lower bound for alternative strategies.
The original-catalog-only retained-history search also failed at a legal 18+18
state with no one-move completion. The combined catalog closes earlier prefixes.
A separate alternate-pivot tactic solver was implemented/tested but never
searched; it is not part of the successful proof. Its unused source is preserved
locally at `/Volumes/2tb/math/.research-cache/unused-tactics-snaky19-20261015-a/`
and omitted from the committed artifact. Constructor intermediate card copies
are likewise generated/ignored; the one delivered final copy is in `certificate/`.

## Working location

Read `RESULT.md` and `MANUSCRIPT.md` for the completed result. Reference source checkout is
`/Volumes/2tb/math/.research-cache/gotrevor`, pinned to
`b18ed32473a6a22ebfdda98da62d61b8b1590c1e`; it is not a second product checkout to edit.
Use the isolated worktree above for all changes and local commits.


## Publication completeness recheck

On 15 October 2026, a separate publication check started from public main at
`4749c87741c668bc2ea6541f5c417af8d7636203`. The exact certificate and recorded
formal-source hashes matched the kernel audit. A fresh standard-library
`reproduce.py --reconstruct` run passed all 31 tests and both corruption controls,
and regenerated the identical 3,468-card certificate. The existing complete
Lean kernel build was not repeated; no mathematical or formal source changed.

The pinned upstream Sieben attribution and permission notice is now included
locally as `reference/sieben-UPSTREAM-README.md`, with its hash and provenance.
The repository is public. `publication/X_POST.txt` contains a 270-character
standard-length announcement, counting the URL as 23 characters, plus detailed
credits and a follow-up. It is ready-to-post text, not a posted X status.
