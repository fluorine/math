# Research state — 15 October 2026

Integrated publication revision: the 12-page PDF includes the exact-seven
proof, generic-cap profiles, and the matched cap-seven comparison. Both the
desktop compiler and Tectonic succeeded; the final rendered pages were
checked and Tectonic reported no warnings. The combined reproduction passed
in 25.622 seconds, including all 63 source hashes and both historical and
current exact-power certificates. The updated independent certificate matches
the final TeX hash. The repository was confirmed public through an
unauthenticated GitHub API request. The external-review prompt is omitted
from the public files at the user's request; the X announcement remains a draft.

Follow-up review of public commit `00820a6`: three fresh-context AI agents
and the primary reviewer checked the labels, profile proof, and arithmetic.
No proof gap or certificate discrepancy was found. A direct cyclic-orientation
corollary gives a uniform cap fourteen and exact cap seven at q=1001.
Using seven in both analyses preserves a strict gain; see
[FOLLOWUP_REVIEW.md](publication/FOLLOWUP_REVIEW.md). A fresh checkout fetched
and hash-checked all 63 sources and passed the existing reproduction.
`checks/independent_audit.py` separately passed exact arithmetic and rational
logarithm checks; `checks/independent-audit.json` preserves its output.
The user authorized publication of these follow-up improvements and their
integration into the note. The current TeX/PDF include the cyclic bound,
the exact-seven witness, the profile theorem for every cap $K\ge3$, and the
matched cap-seven comparison. The original cap-fifteen certificate is retained.
The main reproduction command now includes the separate arithmetic audit.
No human referee or Lean verification is claimed.

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
most 15 vertices for arbitrary orientations. The cyclic regular orientation
sharpens this to $H+1$, with $H=\lceil\log_q k\rceil$: at most fourteen
uniformly, attained at q=3, and exactly seven at q=1001.
The generator evaluates each edge in O(log²M) bit operations, O(logM) space.

Final profile theorem: see the six S0 and five J0 branches in the note,
stated for every coherence cap $K\ge3$; PROFILE.md gives the original cap-15 proof.
Most target repairs are joint; source-head reassignment and candidate-count
tradeoffs give the full improvement. Local counterexamples delimit stronger
false shortcuts without claiming global sharpness.

Fixed certificate: q=1001, d=17, M=169000000, r=13000,
k=57122000000000001, c=164900179. Identical B and 373-digit dimension;
the current cap-seven comparison improves the certified exponent from
2.0154112468376777104... to 2.0154115475113140209.... The original cap-fifteen
comparison, 2.0154109030915821803... versus 2.0154115473114784763...,
remains in checks/seed-certificate.json. The OR-copy count is held fixed;
it has not been reoptimized for seven. Exact integer powers also give alpha>2.0154.
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

The first publication's 10-page PDF compiled successfully with the desktop compiler and
Tectonic. Its rendered layout, displayed certificate enclosures, local links,
and short-thread lengths were checked. No mathematical implementation changed
during publication preparation; the recorded reproduction remains applicable.
That version explicitly disclosed the additional coherent-set bound eight
for q=1001 after deleting seven common leading digits. Both saved recurrence
calculations in its original certificate left that label-specific improvement
unused. The current note incorporates the follow-up exact-seven argument and
uses seven on both sides of the principal comparison.

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
No global optimum or unqualified historical priority is claimed. The initial
publication and follow-up review are preserved in Git history. The integrated
revision passed its focused checks and has explicit authorization for a
fast-forward publication to public main. Git history preserves the earlier
results without modifying the shared local main checkout.
