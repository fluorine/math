# Source and literature audit

The completed follow-up comparison, including Cole–Vishkin, canonical Ramsey,
star-colored graphs, lexicographic products, and the exact profile-proof
boundary, is in [the publication novelty audit](../publication/NOVELTY_AUDIT.md).
The inventory below preserves the initial source-recovery audit.

Audit date: 15 October 2026 (Europe/Amsterdam). Independent reader: verifier
agent; saved and integrated by primary. No priority guarantee is implied.

## Exact versions

- OpenAI/math reference and current remote HEAD both
  `1581d4cbdd69a0faf34b2089614fe2a814316a6a` (HEAD checked with git ls-remote).
  [Preprint](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-superquadratic-separation-between-sensitivity-and-block-sensitivity-September-25-2026)
  and [scope note](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/docs/132.md).
  The scope note is under **lean/docs**, not root docs. All four manuscript
  sections and 51 sensitivity Lean modules were recovered. Their exact
  URLs, sizes, and SHA-256 hashes are in manifest.json; files.txt pins the
  fetch inventory. Raw cache is local and ignored.
- [Meiburg, arXiv:2608.00851v1](https://arxiv.org/html/2608.00851v1), submitted
  1 August 2026; no newer version appeared on the arXiv record. The headline
  theorem concerns spectral sensitivity, not ordinary sensitivity. It
  describes nonconstructive labels and a cyclotomic heuristic. Neither is
  the proved generator for this different head-label contract.
- Timeroot/BS_Lam remote HEAD
  `7bd39a8d41ee7910d3296d0477ad18f8fff9d870`, dated 28 August 2026.
  [Status](https://github.com/Timeroot/BS_Lam/blob/7bd39a8d41ee7910d3296d0477ad18f8fff9d870/Status.md).
  Its proof-build claims were inspected, not rerun locally.
- [arXiv:2609.23781](https://arxiv.org/abs/2609.23781), on elementary symmetric
  Boolean functions, is adjacent literature with a different function class.

## Search queries

Initial refresh used the following public web queries, relying on primary
sources for mathematical claims:

1. `"arXiv:2608.00851"`
2. `"Timeroot" "BS_Lam"`
3. `OpenAI math sensitivity block sensitivity 132`
4. `"sensitivity" "block sensitivity" "generator" 2026`
5. `"superquadratic" "sensitivity" tournament explicit construction`
6. `"ordinary sensitivity" "profile" tournament`
7. `"sensitivity" "block sensitivity" "2026" "explicit"`
8. `"sensitivity" "block sensitivity" "gate" "profile"`
9. `"superquadratic separation" "sensitivity" -site:reddit.com -site:emergentmind.com -site:studylib.net`
10. `"BS_Lam" "generator"`

No matching proved efficient exact-contract generator or stronger ordinary
profile theorem surfaced. This does not exclude unindexed work, different
terminology, unpublished results, or elementary consequences recognized
elsewhere. GitHub's root recursive tree was truncated; targeted directory
retrieval, not absence from that tree, determined formalization scope.
Unauthenticated API rate limits were encountered; raw pinned downloads and
git ls-remote remained available. No credentials were printed or changed.

## First-difference antecedent and novelty boundary

The proposed generator uses a classical method, not a newly invented
coloring technique. Gishboliner–Milojević–Sudakov–Wigderson explicitly use
the standard binary hypercube coloring by first differing coordinate in
the proof of Theorem 2.3 of
[arXiv:2410.08644v1](https://arxiv.org/html/2410.08644v1).
Their stated setting is undirected canonical/weak-lexicographic copies.
Related directed-coloring context includes
[Flashes and Rainbows in Tournaments](https://people.maths.ox.ac.uk/scott/Papers/flashesrainbows.pdf).

An even closer methodological antecedent is Cole–Vishkin deterministic
coin tossing: position of a differing bit together with the source's bit.
See [Vishkin's lecture notes, p.72](https://users.umiacs.umd.edu/~vishkin/PUBLICATIONS/classnotes.pdf)
and the [1986 paper DOI](https://doi.org/10.1016/S0019-9958(86)80023-7).
These concern local asymmetry on lists/rings, not the arbitrary-orientation
head-coherent tournament bound proved here. Additional searches included
`tournament head canonical coloring`, `tournament monochromatic first differing`,
`tournament in-monochromatic`, and `tournament head lexicographic`.

The precise candidate contribution here is the arbitrary-orientation
head-coherence bound h+2 for first-difference labels that also encode the
source digit (or its injective difference from the fixed head digit), and
its succinct instantiation of the exact family-132 parameters. The initial
targeted comparison did not locate this exact theorem. Claim only that
explicit adaptation and application, with provisional novelty; do not
claim invention of first-difference coloring, gated tournaments, OR balancing,
or composition amplification.
