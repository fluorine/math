# Research state

Updated 2026-10-15. Primary objective **incomplete**: no 19-move certificate yet.

## Location and ownership

- Repository: `/Volumes/2tb/math`, original HEAD `7566886575317521d0b9510c7ef1198845ccec4f`.
- Isolated worktree: `/Volumes/2tb/math/.worktrees/snaky19-20261015-a`.
- Branch: `research/snaky19-20261015-a`.
- Scope: `topics/snaky/`; other sessions have separate worktrees. Do not modify them.
- Root owns specifications, integration and result claims. Constructor owns
  `constructor/`; independent verifier owns `verification/`. Challenger initially
  reads sources without writing. No publication or remote push authorized.

## Host and limits

Apple ARM64 Darwin 25.3.0, 8 logical CPUs, 16 GiB RAM. Initial disk availability
368 GiB on `/Volumes/2tb`. Swap already used about 4.65 GiB; other workloads include
compression and Python tasks. Start with one CPU-intensive experiment at a time,
at most two computational threads, and modest memory use. Do not run the upstream
15×15 tree checker (documented 20 GB RAM) under this resource envelope.

Tools observed: Git 2.50.1, gh 2.92.0, Apple clang 21.0.0, system Python 3.9.6;
Homebrew Python 3.12/3.14 available. Lean/lake absent from PATH. Prefer Python
stdlib and local executables. No paid or cloud compute.

## Completed

- Read task brief and inspected host and clean initial repository.
- Cloned repository and created isolated worktree/unique research branch.
- Refreshed novelty audit before strategic search; see `NOVELTY.md`.
- Read exact 20-move Lean statement, card rules, shape and 15×15 result.
- Saved 764,733-byte baseline certificate with provenance, not as a new result.

## Active frontier

1. Constructor reconstructs critical card dependency routes with exact coordinates.
2. Verifier implements independent card semantics and rejection controls.
3. Challenger investigates a distinct improvement mechanism and semantic pitfalls.

Next decisive step: verify the baseline and identify which actual 20-move routes
remain after retaining full Maker history. Try interventions at those bottlenecks,
with independently accepted declarative certificates. No strategy experiment has
run at this checkpoint. No failed approach yet.

## Resume

Read this file, `NOVELTY.md`, and agent-produced reports under `constructor/` and
`verification/`. Reference source checkout is
`/Volumes/2tb/math/.research-cache/gotrevor`, pinned to
`b18ed32473a6a22ebfdda98da62d61b8b1590c1e`; it is not a second product checkout to edit.
Use the isolated worktree above for all changes and local commits.
