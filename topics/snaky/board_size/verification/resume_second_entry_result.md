# All 79 second-entry source configurations are pair-replaceable

Publication scope: this is a curated research note. Large search decks,
solver logs, and unrun adapters named in the historical text remain outside
this compact package. Included finite receipts and the Lean theorem sources
are distinguished in [the closeout guide](../README.md).


The independent continuation audit accepted all 15 new positive replacements.
Together with the original 64 accepted replacements, `all79_retired` is now
**true** for the exact source parent below. This supersedes the unresolved
status in `all_second_entry_result.md`; that historical note and every original
forest remain unchanged.

This is a structural reduction of a fixed admission mechanism. It does not
solve 79 physical game branches, prove a ten-board game outcome, or establish
an impossibility result from any earlier solver's UNSAT observation.

## Exact reduction

The source parent is file 10, node 214420, in the checked
`release-9x9/snaky-9x9-d3.json.gz` certificate. Stored Maker `{21}` and Breaker
`{22}`, under `(x,y) -> (x,8-y)`, give virtual G=`{63}`, Q=`{64}`. The inventory
retains all 79 literal legal second Maker entries, their actual certified
replies, full resulting source colors and the same frame. Physical play starts
empty; source colors are not physical stones.

For each of these 79 resulting states, consider any complete admission with
`K ⊆ C \ (G ∪ Q)`, where C is the coordinate square 0 through 8. A physical
Snaky E is core-covered if an eligible literal source F has
`F \ G ⊆ K ∩ E`. Every other E must contain a protected subset of a pristine
exterior component. All full component domains are mutually disjoint and
disjoint from K. Different source F and physical target E are included.

The accepted matching P for that source state covers every source trace not
REFUTED by the sound necessary-membership rules, **including every UNKNOWN
trace**. For any admissible K, a core-used trace cannot be REFUTED. It therefore
contains a pair of P lying wholly in `K ∩ E`. Install only those pairs of P
wholly contained in K, remove the source core and keep all exterior components
and their full domains. Disjointness and every target assignment are preserved.
Every replacement pair has an explicit identity in the same accepted ordinary
catalog. The 79 states have separate matchings; no common matching across all
states is asserted.

Consequently this complete fixed second-entry source family adds no
admission-existence power beyond the same exterior catalog plus ordinary
pairs. This conclusion allows arbitrary exterior components to which the
reviewed necessary-rule argument applies; it is not restricted to static
pairings outside K. It does not extend to another source opening, another
reply policy, overlapping component domains or unrestricted Breaker play.

## Checked evidence and execution

The continuation copied only the 15 unfinished forests. It preserved every
old deduction prefix, every old split and every REFUTED root. The independent
checker imports no constructor or matching search. It checked exact copied
prefixes, replayed the changed trees, rebound all 79 source children and all
432 targets, and validated positive replacements for all cross-target
incidences. The original 64 retirements were reused through their accepted
audit and exact branch hashes.

| Quantity | Result |
| --- | ---: |
| Source configurations retired | 79 of 79 |
| All retained source seed roots | 19,160 |
| REFUTED / OPEN / UNKNOWN | 11,911 / 726 / 6,523 |
| New nodes / deduction steps | 6,746 / 24,066 |
| Combined base and continuation nodes / steps | 28,610 / 172,079 |
| Source-to-physical incidences | 19,186 |
| Non-refuted incidences covered by the 15 new replacements | 494 |

The two `88→43` and `87→43` cases closed by a fresh one-second matching allowance
on their unchanged remaining families. The other 13 received additional
closure/refutation work before positive matching. No new browser03 lemma was
used. OPEN and UNKNOWN remain visible and are not treated as feasible masks.

The 12 focused controls passed in 0.011 seconds after one diagnosed fixture
correction: an intended prefix-only example used two overlapping pairs, whose
extra contradiction the constructor correctly found. The corrected fixture
uses disjoint pairs. Both test logs and both launch manifests are preserved;
production constructor and checker sources did not change.

Construction ran once as PID19701: 22.353 process CPU seconds, 23.381 guarded
wall seconds, 62,701,568 bytes peak RSS, no pressure events. Independent replay
ran once as PID20607: 2.075 process CPU seconds, 2.524 guarded wall seconds,
87,474,176 bytes child peak RSS, no pressure events. Its first preflight held
before spawning due to host pressure; that was not a replay attempt.

The construction allowed 240 internal/250 external CPU seconds and 840/900 wall
seconds; branch allowances total at most 210 CPU seconds plus overhead. There
is no unused-budget reserve phase. Replay allowed 44/45 CPU and 225/240 wall
seconds. Both used nice 19, one thread, the unchanged host-pressure guard and
a 200 MiB sampled RSS cap. All final source/input pins still matched.

| Evidence | SHA256 |
| --- | --- |
| `resume-second-entry-membership-01/manifest.json` | `a0d9f9bfee99726c41b8e5a37749015a5883c63f691d9aae806d54a7a7ad226f` |
| `resume-second-entry-membership-audit-01.json` | `485ad978e6b12bf708f8da072f0159d37f0ea0fe570774541ed6ada37a15fb0c` |
| `resume-second-entry-membership-01.launch-manifest02.json` | `0ad85023fbf15c1b323387f657f9dee03a82315576337cd7d73e9e3119b8b4ca` |
| `resume-second-entry-membership-01.execution.json` | `3a1b5ee946748acae6bc771a3915bc869cb6bed6c36f0673dfbbaafb006dcf82` |

For reproduction, use the exact argv, interpreter, environment and pins in the
launch manifest with fresh output paths and the applicable resource gate. The
independent entry point is `check_resume_second_entry_membership.py --manifest
resume-second-entry-membership-01/manifest.json --output <fresh-audit>.json`.
New timing-limited construction can produce a different forest; replay of the
preserved candidate establishes the stated result. No further run is implied.

## A distinct next source choice (historical proposal)

This proposal was subsequently investigated. The completed
[e1 replacement theorem](../../formal/Snaky/E1Result.lean) and
[kernel audit](../../formal/kernel-e1-closeout.json) supersede the unexecuted
status below. They give same-domain replacement under explicit compatibility
and membership hypotheses, not an empty-board defense.

Prefer an already bound different first source opening over another sibling
or a fourth ghost descended from this retired family. The accepted
`breaker/core-opening-citation.json` (SHA256
`9a178f5fedd2075943d9e0654776ecc42cb4da671892cf7adacbc76edb8d5410`)
binds `release-9x9/snaky-9x9-e1.json.gz`, root 229423, stored M=`{4}`, B=`{40}`.
The same reflection gives G=`{84}`, Q=`{44}`. Its explicit stored row
`[3,32,6784]` proposes the distinct virtual continuation `83→55`, hence
G=`{83,84}`, Q=`{44,55}`.

First independently bind the full child `{3,4}` / `{32,40}` by an indexed cache
query, then reconstruct its literal shortened traces and exact cross-target
predicates. The boundary-adjacent ghost pair is a different geometric channel;
its usefulness is unproved. A positive common pair cover of all surviving
traces would retire it just as above. A remaining non-pairable shortened family
would justify a specific membership lemma or admission attempt, not a game
claim. This next lookup or search has not been executed here.

The e1 root stores representative second moves, rather than a literal
79-entry table. Any later full-table expansion must validate the accepted
symmetry/irrelevant-move dispatch and transport the entire colored state.
Do not feed these representative rows into the current exact-79 interface.
