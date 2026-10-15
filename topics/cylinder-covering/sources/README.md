# Pinned primary sources and attribution

The 91 files listed in [manifest.json](manifest.json) are unmodified snapshots
from [OpenAI math](https://github.com/openai/math) at revision
[`1581d4cbdd69a0faf34b2089614fe2a814316a6a`](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a),
checked on 15 October 2026. The upstream Apache-2.0 license is retained in
[LICENSE](LICENSE). The manifest records immutable source URLs, SHA-256 hashes,
and Git blob IDs when available. The reproduction command checks these hashes.

The four primary manuscripts, dated 27 September 2026, are:

- [Finite angular cylinder covers below the half-area bound](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Finite-angular-cylinder-covers-below-the-half-area-bound-September-27-2026).
- [Finite cylinder approximation of ruled sets](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Finite-cylinder-approximation-of-ruled-sets-September-27-2026).
- [Slope-field perturbations of the two-cylinder covering](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Slope-field-perturbations-of-the-two-cylinder-covering-September-27-2026).
- [Finite triangular approximation of radial sweeps](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Finite-triangular-approximation-of-radial-sweeps-September-27-2026).

The selected Lean modules supply definitions, earlier footprint estimates,
source sufficient conditions and comparison constants. They are prior-art
snapshots, not a formalization of this repository's new quartic/secant theorem.
The broad comparison-source audit inspected these proofs as mathematical text.
The later [formalization addendum](../formal/README.md) checks the new primary
quartic/secant theorem and its eight-module OpenAI geometric dependency closure;
it archives those originals separately and validates every header-only adaptation.
That formalization is distinct from this larger prior-art evidence archive.

The upstream `CONTENTS.md`, manuscript READMEs and other snapshots retain
links to their original repository layout. Some link targets are not included
in this selective archive. Use the immutable upstream links above, or each
manifest entry's URL, for navigation. Do not alter the snapshots to repair
archival links, because that would invalidate their source hashes.

The new proofs, constructor code and independent verification are one level
above this source archive. [NOVELTY.md](../NOVELTY.md) distinguishes inherited
geometry, immediate source corollaries and the additional quantitative estimates.
