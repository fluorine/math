# Research state — 15 October 2026

Mathematical targets achieved: succinct proved uniform labels for family 132
and a strictly stronger coupled-profile theorem. Both survived independent
audit. Historical novelty remains provisional; see NOVELTY.md and RESULT.md.

Branch: `research/sensitivity-20261015-01a13f19`; base `7566886`.
Other local worktrees and the local main checkout are untouched. The user
approved publication after reviewing the complete package. Commit `fe3e100`
was pushed without force to public `shjvandekamp/math` main on 15 October 2026.
The remote commit and PDF blob were checked against the local copies.

Host inspected: Apple arm64 Mac mini, macOS 26.3, 8 physical/logical cores,
16 GiB memory; external volume had 368 GiB free. A pre-existing zstd process
was consuming about two CPU cores. Our experiments remain serial, one CPU
thread, bounded in runtime and memory. Python 3.9 stdlib, git, clang, cmake,
node, z3 and gh are available; lean/lake and uv were not on PATH. No
dependency installation or cloud computation has occurred.

Completed: repository isolation, all pinned source recovery, pre-experiment
novelty audit and follow-up antecedent search, generator/proofs, profile
refinement, baseline scan, exact/certified seed comparison, independent
audit, manuscript, and full integrated reproduction. The raw source cache
is ignored; sources/manifest.json records 63 file hashes. No Lean build ran.

Completed bounded roles (disjoint ownership):

- Primary: integration, baseline arithmetic, NOVELTY/STATE/RESULT, source
  manifests, final proof-status decisions and local commits.
- Constructor: proofs/CONSTRUCTOR.md and checks/label_contract.py.
- Challenger: proofs/PROFILE.md and checks/profile_local.py.
- Verifier: read-only independent source/literature and theorem audit;
  primary saves its findings in proofs/VERIFICATION.md and sources/LITERATURE.md.

Final construction: 13 base-q digits, first-difference position and source
digit ranked excluding the head; q>=3, M=[13(q−1)]². Coherent sets have at
most15 vertices for arbitrary orientations. Use cyclic regular orientation.
The generator evaluates each edge in O(log²M) bit operations, O(logM) space.

Final profile theorem: see the six S0 and five J0 branches in PROFILE.md.
Most target repairs are joint; source-head reassignment and candidate-count
tradeoffs give the full improvement. Local counterexamples delimit stronger
false shortcuts without claiming global sharpness.

Fixed certificate: q=1001, d=17, M=169000000, r=13000,
k=57122000000000001, c=164900179. Identical B and 373-digit dimension;
certified exponent improves from 2.0154109030915821803... to
2.0154115473114784763.... Exact integer powers also give alpha>2.0154.
The latter threshold alone was already available from source formulas.

Reproduction passed using scripts/reproduce.py --fetch-sources. See
checks/reproduction.log. No long-running computations or partial searches
remain. No cloud compute, purchase, or remote merge occurred. Publication used
an ordinary fast-forward Git push after explicit user approval.

Publication preparation adds a standalone typeset mathematical note, a deeper
novelty audit, a public repository overview, and an X announcement draft.
The deeper comparison separates the classical label mechanism and routine
corollaries from the directed avoidance proof and coupled-profile argument.
Historical priority remains provisional. Reviews to date are by AI agents;
the work has no human referee review or formal verification of the new results.

The final 10-page PDF compiled successfully with the desktop compiler and
Tectonic. Its rendered layout, displayed certificate enclosures, local links,
and short-thread lengths were checked. No mathematical implementation changed
during publication preparation; the recorded reproduction remains applicable.
The public note explicitly discloses the additional coherent-set bound eight
for q=1001 after deleting seven common leading digits. Both saved recurrence
calculations leave that label-specific improvement unused, so their comparison
is at the common no-16 contract and does not optimize the actual seed.

Publication package: README.md, publication/sensitivity-note.tex,
output/pdf/sensitivity-note.pdf, publication/NOVELTY_AUDIT.md, and
publication/X_POST.txt. The repository is public and the announcement remains
a draft. Posting to X requires a separate user instruction.

Publication access: the initial HTTPS dry run lacked credentials. GitHub CLI
was subsequently authenticated as `shjvandekamp` through GitHub's device flow,
with HTTPS Git authentication configured. The repository was confirmed public,
and remote main advanced from `7566886` to the approved package `fe3e100`.
The earlier SSH check did not change known hosts.

Optional next research: formalize the new combinatorial theorem in Lean,
obtain external mathematical feedback, or seek better seed/profile parameters.
No global optimum or unqualified historical priority is claimed. All
required deliverables are committed and published; git log preserves the
research history without modifying the shared local main checkout.
