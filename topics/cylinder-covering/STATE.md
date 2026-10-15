# Cylinder-covering research state

Date: 15 October 2026 (Europe/Amsterdam).
The theorem package is complete and has been prepared for public release, with a PDF, standalone LaTeX and a single offline reproduction command.
The user chose published constructions on their proved parameter ranges and
count conventions, rather than every admissible instance of generic methods.

Repository: https://github.com/shjvandekamp/math
Base commit: 7566886575317521d0b9510c7ef1198845ccec4f.
Branch: research/cylinder-radial-20261015-01a13f19.
Worktree: /Volumes/2tb/math/.worktrees/cylinder-radial-20261015-01a13f19.
Initial theorem checkpoint: 7e1150a17b9d0c4d7ef718b44ac142cd137dbc7c.
Main checkout, other topics, worktrees and unrelated processes are preserved.
Publication was authorized on 15 October 2026. The publication branch is
`publication/tetrahedron-20261015-01a13f19`, based on current public main and
preserving the Snaky and sensitivity topics. The verified research checkpoint
is `f96e09461563a7589b24d21304cb6097617d8d29`. This release contains the
completed theorem and supporting evidence; no X post is part of the request.

## Host and resources

Observed arm64 Apple M1 Macmini9,1, 8 logical CPUs, 17179869184 bytes RAM,
368 GiB free on the 1.8 TiB volume, macOS Darwin 25.3.0. Initial memory
pressure reported 39% system-wide free, with competing CPU activity.
One small computation at a time, at most two threads; no unrelated process
termination. Python 3, Git and pdftotext are available. No SymPy, NumPy,
mpmath, python-flint, SciPy, Sage, Lean, Lake or Julia was available on the
inspected paths. No installation was needed. gh is unauthenticated; immutable
raw HTTPS supplied public source files after API rate limits were reached.
No cloud compute, purchases or large cylinder arrays were used.

## Completed mathematics and files

- All four requested manuscripts, relevant Lean dependencies and license are
  pinned at 1581d4cbdd69a0faf34b2089614fe2a814316a6a. That revision was the
  public HEAD when checked. Manifest: 91 files with SHA-256 hashes and Git
  blob IDs when available. Public and targeted source novelty audits found
  no matching certificate; no exhaustive novelty guarantee is claimed.
- NOVELTY.md preserves the pre-experiment specifications, retired routes,
  later source corrections and final classification.
- THEOREM.md proves the quartic continuous cap, sharpness of 9/16 among
  constant quartic corrections, the original radial finite realization,
  unique symmetric full-sweep triangle optimum, and sharp leading 4e/N loss
  over every N-cell midpoint partition in that declared enclosure class.
- SECANT-THEOREM.md is the preferred complete finite theorem. Compatible
  secants plus the new explicit residual buffer cover the closed tetrahedron
  for every positive partition and 0<e<1. For e<=1/10, |R-J|<=e*mesh.
  Equal cells give exactly 2N cylinders and |R-J|<=2e/N. N>=ceil(480/e)
  gives R<=1/2-e^2/240.
- On N=ceil(2/e^2), R<=1/2-e^2/60+e^3/2+(9/2)e^4, with strict saving
  throughout e<=1/50. The actual cubic coefficient of this construction is
  1/2, versus sharp coefficient 2 in the full-sweep enclosure class.
- At e=1/10,N=10000, the exact independent area interval is
  [0.499921585997001674,0.499921585997001774]. Maximum finite axis tangent
  is exactly sqrt(3)*e*(1-1/N), with physical tau=2e.
- At e=1/100,N=20000, the new interval is
  [0.499998863418315727,0.499998863418315728]. The old radial enclosure
  at these same parameters was above 1/2. At e=1/1000,N=2000000, the new
  interval is [0.499999983836322736,0.499999983836322737].
- secant_construction.py returns one exact rational cylinder by index;
  construction.py retains the original radial generator.
- verification/verify.py and secant_verify.py independently reconstruct
  the critical identities, rational inequalities and exact power sums.
  Generator checks separately verify physical factors, both families,
  perpendicular projections, vertices and triangle area. No point sampling
  substitutes for universal coverage. No Lean build is claimed.

## Completed published-range comparison

The source-proof audit recovered explicit witnesses missed by the earlier
manuscript-only reading. General angular admissibility with
(10+4E)tau<=eta<=1/480 has actual cost>=1/2-1/5529600000 and full-list count
at least 36864000. Separate direct endpoint/squared and alternative Cartesian
certificates are included. All published radial numerical sufficient ranges
imply the common 9e overlap comparison. The angular maximum-cap comparison
also includes optimizing the retained-mesh old inequality: canonical cubic
coefficients 16,29/2,14 in its respective mesh conventions, not only 100 from
Proposition 6.1.

At the 20000-cylinder benchmark, the combined actual-area/count/angle bounds
cover these identified explicit source sufficient ranges and the prescribed
rational/singular grid, product/log, nilpotent apex and beam-strip recipes.
See RESULT.md and research/published-proof-ranges.md for precise conventions,
with geometric details in the comparison notes. Fixed-positive-margin
families also have a same-count, exact-angle sufficiently-small comparison.

This does not assert that every possible witness of an existential theorem
satisfies the source's numerical witness, or rule out larger valid ranges.
Arbitrary new admissibility results, deletion/merging schemes, changed generic
error allocations and global optimality are outside the selected benchmark.
These boundaries are explicit in the result, not unresolved coverage claims
for the new construction.

## Failed routes and corrections

- Generic effective footprint/count bounds already exist in the Lean source;
  merely extracting them was retired as a novelty claim.
- The initial smaller triangle with effective padding (5/2)e*d is a source
  trapezoid corollary. The quartic cap and sharp optimized enclosure are the
  substantive additions in the first theorem.
- Optimizing full-cell symmetric enclosures or midpoint partitions cannot
  remove their leading 4e/N loss; a proved lower bound motivated secants.
- The old e=.01,N=20000 radial triangles fail to save area; the new secants
  at the same parameters succeed.
- The eta=.001,tau=.2,N10000 angular candidate was initially conditional.
  Its coverage is now proved by the new quartic/secant buffer, extending its
  certified range. It was not certified there by the old source thresholds.
- The candidate estimate delta<=ed/2+2e^2d is false at e=.1,d=e^2;
  the proof uses 21e^2d/10 on d<=e^2, with exact remainder bookkeeping.
- Actual projected bases can be strictly smaller than enclosing triangles.
  A source generic method applied using our new admissibility proof therefore
  defeats any claim of strict dominance over all generic instances. The user
  explicitly chose published proved ranges/count conventions instead.
- Missing explicit source counts never served as a lower bound. The final
  comparisons use actual area, positive retained-grid collars, source error
  allocations, full-list counts or physical strip angles.

## Verification and research checkpoint

Astra workers with disjoint writing scopes supplied construction, adversarial
coverage/baseline analysis, independent verification and targeted source review.
The primary read and integrated all mathematical notes and code. The verifier
reconstructed acceptance calculations independently of the constructors.
Runs are standard-library exact arithmetic and take well below one second;
large counts use power sums, without cylinder allocation.

Reproduce from the worktree root:

    python3 topics/cylinder-covering/verification/verify.py
    python3 topics/cylinder-covering/verification/secant_verify.py
    python3 topics/cylinder-covering/secant_construction.py --epsilon 1/10 --n 10000 --index 0

The final primary run passed both exact verifiers; its outputs are saved in
verification/last-run.txt and secant-last-run.txt. All 91 SHA-256 hashes and
48 available Git blob hashes passed. Relative Markdown links and math
delimiters were checked. The research extension was committed locally as
`f96e09461563a7589b24d21304cb6097617d8d29`, before the publication request. The requested research deliverables are
complete under the user's selected comparison conventions. Optional future research includes nonconstant quartic profiles and
smaller sharp discrete buffers; neither is needed for the delivered theorem.


## Publication packaging

The public entry point is README.md; publication/cylinder-covering-note.tex
and output/pdf/cylinder-covering-note.pdf contain the primary theorem and its
full proof. The supporting optimality and baseline arguments remain in the
linked Markdown manuscripts. reproduce.py checks all pinned source hashes,
runs both exact verifiers and compares their output with the committed records.

The publication audit found no new mathematical blocker. It corrected stale
local-only status, distinguished historical research notes from final results,
and made the source-range/count conventions and non-Lean verification boundary
explicit. The source snapshots remain byte-for-byte unchanged. Public sources
are credited in sources/README.md with the retained Apache-2.0 license.

The 13-page publication PDF compiled successfully with the desktop LaTeX
compiler and Tectonic. Its page layout, main equations and comparison table
were inspected after correcting line overflow; the final Tectonic build has
no layout warnings. Both verifier outputs and all source pins reproduce.


## Lean formalization addendum

The later publication request extends the primary result to a complete Lean
formalization in formal/. Earlier entries above describe the research and
publication state at that time; their no-Lean statements are historical. The
analytical PDF and its open LaTeX source are preserved as published. The current
verification status, exact statement scope and reproducible commands are in
formal/README.md and formal/kernel-audit.json. The eight reused OpenAI modules
have exact archived originals and checked header-only adaptations. All new
geometric and quantitative arguments are in TetrahedronCover/. No X post is
part of this publication.
