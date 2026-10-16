# Universal six-template e1 replacement

Publication scope: this is a curated research note. Large search decks,
solver logs, and unrun adapters named in the historical text remain outside
this compact package. Included finite receipts and the Lean theorem sources
are distinguished in [the closeout guide](../README.md).


The independent finite audit passed once on 2026-10-16. The lead accepted the finite result after reviewing its source and receipt. It verifies Browser03's twenty-second proposal that every
viable core of the exact e1 source can be replaced by an ordinary matching on
the same reserved domain. Here viability means compatibility with a complete disjoint-domain
containment admission, not merely a legal choice of core cells. Neither an
exterior completion nor a physical empty-board winner follows from replacement.

The source remains file12, parent229423, child6784 after stored3/32, reflected
by `(x,y)->(x,8-y)`. Its virtual colors are G={83,84}, Q={44,55}; physical
ownership is empty. K lies in U=[0,8]^2 minus G and Q, using10-stride IDs.
The checker regenerates all432 targets,240 full eligible sources and247
source-to-physical incidences, including all seven cross-source incidences.
A source F is active exactly when its entire trace A=F minus G lies in K.
No intersection or shortened-only approximation replaces that condition.

Two accepted forbidden sets are used:

```
A0 = {42,52,53,63,73}
A1 = {72,73,74,85}
```

The accepted two-phase audit supplies the necessary row lemma: K contains at
most one run R_i={30+i,...,33+i},0<=i<=5. Its28 projected cases and exact
512-row partition are bound without rerunning those proofs. The new checker
independently replays all16 memberships of24,33,34,64 around
D1={43,53,63,73,74}. Three literal full targets, with complete source predicates,
give a singleton, a two-edge fork, or the three-claim line33/64,34,completion24/44.
All outside reply classes and immediate/final claims are included. This proves
D1 cannot lie in a viable K; all sixteen finite replay cases passed.

For X={65,66,67,68,74,75}, two source-free physical targets have hooks58/59
and78/79. Cells59 and79 lie outside U. All four memberships of58,78 are checked;
each violating case gives an uncovered projected singleton. Thus X implies
58,78 are absent from K. These are exclusions from the reserved core, not
physical Breaker claims. All these attacks concern necessary projected exterior
obligations, not physical Snaky wins.

Let M_epsilon be the accepted32-pair phase template. Select epsilon=(i+1)mod2
when the unique R_i is contained in K, or0 when no run is contained. The six
literal templates are the two phases of these three modes:

```
H0 = M + {72-73}
H1 = M - {71-82,74-75,76-85}
       + {70-71,73-74,75-76,81-82,85-86}
H2 = H1 - {57-67,58-68,77-78} + {67-68,57-77}
```

They have33,34,33 pairs respectively. Each complete template must be a matching
on U; every pair must occur inside a literal physical target. Mode0 applies
when {73,74} is not contained in K; mode1 when {73,74} is contained but X is not;
mode2 when both are contained. The128 memberships of the seven determining
cells independently check that these modes are exhaustive and disjoint.

The universal check avoids enumeration of the77 allowed core cells. Fix an
exact membership R on the nine row3 cells, a mode, and one source trace A.
Let P be that mode's mandatory positive cells. The smallest core activating
this source in that case is K_min=R union P union A. It must avoid all row3
cells not in R. The other necessary constraints are all forbidden subsets:
A0,A1,D1,X union{58},X union{78}, plus {73,74} in mode0 or X in mode1.

If K_min contains any forbidden set, every larger core contains it too. No
compatible core in that exact row/mode case activates A. Conversely, if
K_min avoids those sets and the negative row cells, K_min itself satisfies
all the stated necessary constraints and the exact mode. This is compatibility
with the checked constraints, not a claim that K_min has an exterior admission.

For every compatible case, the chosen template must contain a pair p inside
the full trace A. Any actual core in that case activating A contains p as well.
Therefore p survives restriction to pairs entirely inside K. Every associated
physical target E contains A and hence p, even when E differs from F. The
checker tests all463 surviving row masks, all three modes, all240 sources and
all247 incidences:333,360 source cases and343,083 incidence cases. Its compact
evidence uses source-ordinal bitmaps and one six-template pair-witness matrix;
it does not save hundreds of thousands of duplicate cores.

This argument proves the conditional implication

```
complete exact-e1 admission
    => complete admission with an ordinary matching core on the same K.
```

Keep every exterior controller and its entire domain unchanged. All of K,
including unmatched cells, stays reserved. The matching invariant says that
every pair with a Maker stone also has a Breaker stone after the round. An
entry into an unblocked pair has a fresh mate available. A previously blocked
pair or unmatched entry permits a legal filler, whose extra Breaker ownership
cannot destroy protection. Interleaving advances only the active component;
no response after an immediate winning or exhausted final claim is invented.
Thus replacement requires neither physical ghost ownership nor support release.

This is a reduction of the exact source's advantage within the stated
construction class. It does not exclude matching-core/exterior admissions,
does not alter any frozen global catalog, and does not decide empty10 or empty14.
A failed coverage case would preserve its explicit minimal-core witness; it
would not automatically establish viability or a physical game outcome.

The single finite check used 12 internal / 15 outer CPU seconds, 50 internal /
60 guarded wall seconds, 150 MiB, nice 19 and one thread, with a fresh shared
resource gate.
No solver or adaptive core search ran. Controls exercised omitted full/cross sources,
wrong phases/modes, deleted repair pairs, the essential X58 exclusion, D1
forced/outside/final cases, false physical ghost ownership and overlapping pairs.

Report [e1-phase-template-universal-01.json](../verification/e1-phase-template-universal-01.json)
has SHA256 `c437e5c196161365d87beeaa2dae1b4eff88db7876be3a522fe8de3c1663fda3`.
It classifies 333,360 source cases: 195,169 compatible and 138,191 incompatible.
All 343,083 incidence cases passed, including 203,966 compatible cases and 8,797
compatible cross-source cases. The 16 D1 cases, four X cases, 128 mode assignments,
twelve negative controls and the two-branch final-claim control all passed.

Child 61419 exited 0 after 1.803003 process CPU seconds and 2.100107 guarded wall
seconds, with 85,819,392 bytes sampled peak RSS and no guard events. The fresh
two-sample gate was 53.82% / 52.88% idle; direct swapouts stayed at 18,875,158.
The immutable [execution receipt](../verification/e1-phase-template-universal-01.execution01.json)
has SHA256 `8cb372e67d2f840e10d64d665282e11df18cec9a6f4a7b854d3d7e2e59a5ea79`.
Checker SHA256 remains `c5103aea775f701496dce0f8caccdd598c25637876fa0f98f25651b5916af125`.
The receipt-bound original note is preserved as
e1_phase_template_universal_pre_audit.md (historical local artifact; not included),
SHA256 `442d6e59f6f894872f1a1476871e6b4d5c30f3c5778d80b918e45927594b19ce`.
This later documentation update does not change the receipt or audit inputs.

From the repository root, with fresh output:

```sh
cd topics/snaky/board_size
repro_dir="$(mktemp -d /tmp/snaky-e1-universal.XXXXXX)"
python3.12 -B verification/e1_phase_template_universal.py \
  --output "$repro_dir/report.json"
```
