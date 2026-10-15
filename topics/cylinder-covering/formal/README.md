# Lean proof of the finite tetrahedron cover

The central geometric theorem is `TetrahedronCover.tetrahedron_20000` in
[Result.lean](TetrahedronCover/Result.lean). It states that the explicitly defined
`benchmarkFamily : Fin 20000 → TriCylinder` covers every point of the closed
regular tetrahedron and that its actual normalized total base area lies in

```
[499921585997001674 / 10^18, 499921585997001774 / 10^18].
```

`TriCylinder` requires a unit axis and a compact, nondegenerate triangular base
in its perpendicular plane. Area is Euclidean two-dimensional Hausdorff measure;
the denominator is the minimum orthogonal projection area of the tetrahedron.
Neither coverage nor the geometric area formula is a hypothesis of the result.

The [machine-readable audit](kernel-audit.json) and [verification transcript](kernel-audit.txt)
record the 2026-10-15 verification: all 25 local proof modules were freshly
compiled and separately replayed, all 12 public theorem audits reported only
`propext`, `Classical.choice` and `Quot.sound`, and both negative controls were
rejected at their proof obligations. The independent exact-arithmetic checks
and generated-certificate comparison also passed. Fresh compilation and the
final replay were separate invocations on identical proof sources and compiled
artifacts; the record explains the resource adjustment between them.

## Reproduce

Use the official [Lean 4.34.1 toolchain](https://github.com/leanprover/lean4/releases/tag/v4.34.1) on macOS or Linux. The committed `lean-toolchain` and
`lake-manifest.json` pin the compiler and all nine packages, including mathlib
at `d13f23b723b8a846827a245b89c10fc7d3f11612`.

From a clean checkout, install the pinned dependencies and their official cache:

```sh
cd topics/cylinder-covering/formal
lake update
lake exe cache get Mathlib
git diff --exit-code -- lake-manifest.json
cd ../../..
```

Then run the complete audit from the repository root:

```sh
python3 topics/cylinder-covering/reproduce.py --formal --fresh
```

If Lean is not on `PATH`, append `--lean /absolute/path/to/lean`. Python 3.9 or
later and its standard library suffice for the scripts. Dependency installation
needs network access; subsequent checks use the installed, pinned dependencies.
The independent exact-arithmetic checks can also run without Lean:

```sh
python3 topics/cylinder-covering/reproduce.py
```

For a focused formal check:

```sh
python3 topics/cylinder-covering/formal/build.py \
  --target TetrahedronCover.Audit --fresh --replay --negative-controls
```

The driver resolves the actual toolchain when `lean` is an elan proxy.
The build uses one compiler process and one computational thread, with low
scheduling priority. A shared lock serializes concurrent invocations. Each module
has a 240-second wall limit and a sampled 2300 MiB resident-memory guard. Lean's
separate internal allocation limit is 3072 MiB; it is not the process RSS limit.
Only the build's own child process is stopped when a limit is reached.

Local outputs and logs stay under ignored `.cache/build/`; Lake packages remain
under ignored `.lake/`. Resume hashes cover source files, local dependencies,
compiler identity, the package lock, and all generated `.olean` parts. `--fresh`
rechecks every local proof module without using this resume cache. It does not
rebuild mathlib itself. Every dependency checkout must match the committed
revision and have no modified tracked source files.

## Proof organization

| File | Mathematical role |
| --- | --- |
| [Definitions](TetrahedronCover/Definitions.lean) | Quartic cap, cell geometry, explicit local padding and area term |
| [Algebra](TetrahedronCover/Algebra.lean), [Secant](TetrahedronCover/Secant.lean) | Exact quartic identity, perturbation bounds, padding absorption and universal overlap |
| [Partition](TetrahedronCover/Partition.lean) | Arbitrary positive partitions, including endpoints and zero-radius first crossings |
| [Geometry](TetrahedronCover/Geometry.lean) | Closed-body coverage, actual triangle bases, Hausdorff area, normalization and exact maximum angle tangent |
| [Estimates](TetrahedronCover/Estimates.lean), [Continuum](TetrahedronCover/Continuum.lean) | Reciprocal-square-root bounds, exact integrals, integrated cell errors and finite-sum error estimates |
| [Schedule](TetrahedronCover/Schedule.lean) | Effective counts, strict saving and an explicit two-sided quartic asymptotic remainder |
| [Nonuniform](TetrahedronCover/Nonuniform.lean) | Mesh-dependent error bound for arbitrary positive partitions |
| [InverseSqrt](TetrahedronCover/InverseSqrt.lean), [BenchmarkPolynomials](TetrahedronCover/BenchmarkPolynomials.lean) | Exact polynomial certificates and telescoping sums |
| [Benchmark](TetrahedronCover/Benchmark.lean) | Reflection pairing of every actual cell and the complete numerical enclosure |
| [Result](TetrahedronCover/Result.lean), [Main](TetrahedronCover/Main.lean) | Public theorems about the physical cylinder families |
| [Audit](TetrahedronCover/Audit.lean) | Exact public theorem types and their axiom dependencies |

The asymptotic statement is made quantitative: on the specified ceiling count
schedule the absolute error from `1/2-e²/60+e³/2` is at most `(9/2)e⁴` for
`0<e≤1/10`. This gives the claimed `O(e⁴)` conclusion with an explicit constant
and range.

## Exact numerical certificate

[generate_certificates.py](tools/generate_certificates.py) constructs rational
polynomials; it is outside the trusted proof boundary. Lean checks all generated
identities with `ring` and all final rational inequalities with `norm_num`.

The degree-eight and degree-nine polynomials bound `1/sqrt(1+z)` on `[0,1]`.
Their residuals and their signs are certified by exact polynomial identities
with nonnegative coefficients in the Bernstein basis. Squaring and positivity
then prove the square-root inequalities. No numerical approximation to a square
root is accepted as a premise.

For the positive half of the symmetric grid, each polynomial area bound has a
rational polynomial discrete antiderivative. Lean proves its difference identity
for every real argument, telescopes the 5000-term sum by induction, and checks
the endpoint rationals. `Benchmark.lean` proves the cap formula, denominator,
reflection pairing and pointwise inequalities for all 10,000 cells. The final
geometric bridge includes both cylinders from every cell.

The negative controls require Lean to reject a falsely lowered upper bound
`0.4999` and a changed Taylor coefficient. Rejection must occur at an unsolved
proof obligation, rather than a missing import or a malformed command.

## OpenAI provenance and trust boundary

The original geometric infrastructure comes from
[openai/math at revision 1581d4c](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a).
The eight exact source snapshots live in [upstream](upstream), with SHA-256,
Git blob IDs and source URLs in [upstream-manifest.json](upstream-manifest.json).
Their Apache-2.0 license is retained in [LICENSE.upstream](LICENSE.upstream).
The larger source and manuscript archive remains in [../sources](../sources).

The active `OAI/` copies preserve every original definition, theorem and proof
body. A deterministic, checked transformation adds Lean's module/public/expose
headers. Two umbrella `import Mathlib` lines are replaced with explicit import
aggregators. This avoids loading private data from every transitive library;
it does not weaken theorem hypotheses or introduce new mathematical axioms.
`build.py` rejects any other difference from the pinned originals.

The new mathematical work is in `TetrahedronCover/`. The axiom audit is expected
to contain only Lean's usual `propext`, `Classical.choice` and `Quot.sound`;
`build.py` treats any other axiom as a failed audit. There are no proof
placeholders, custom axioms, `native_decide`, or unsafe declarations in the local
proof sources.

`--replay` runs a minimally adapted copy of Lean's official `LeanChecker.lean`
separately on every local module, including the adapted OAI modules. It replays
the safe, nonpartial declarations independently of the tactics that constructed
their proofs. An ordinary run may reuse recorded replay results for identical
source and compiled artifacts; `--fresh` forces every compilation and replay.
The proof-source checks reject unsafe and partial declarations. It uses the same Lean kernel, not a
second proof-assistant implementation, and treats the pinned standard library
and mathlib imports as dependencies.

The [replay driver](tools/KernelReplay.lean), its [exact upstream source](tools/upstream/LeanChecker.lean)
and [pinned adaptation manifest](tools/replay-manifest.json) are included. The
only change selects normal exported import semantics for module targets, passing
that level consistently to both import functions. Explicit `import all` remains
respected. The original driver defaults to transitive private imports even for
module targets, which exceeded this host's memory budget. All of the target's
exported/server/private parts and the kernel `replay` call remain unchanged,
with trust level zero and persistent-extension initialization disabled. The driver itself
uses the upstream unsafe IO implementation to read object files; it is checking
the safe mathematical declarations, not contributing a theorem or axiom.
`build.py` verifies that this is the exact recorded adaptation. Compiler/kernel correctness and the normal
foundational axioms remain part of the trust boundary.

The formal scope is the primary finite-cover theorem and its quantitative
estimates. The source-comparison audit, historical novelty assessment, and
supplementary optimality results for other restricted construction classes
remain the separately identified written and exact-arithmetic arguments in the
parent topic; they are not silently included in the Lean theorem claims.
