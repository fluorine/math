# Same-panel extension: broader filtered laws

Contract frozen on 2026-10-15 before extension computation. The verified finite
activity result is the publication baseline, merged in GitHub PR #2. The
extension is local. The frozen search contract is preserved below; the
construction and its current verification status follow it.

## Unchanged observations

Use exactly the event grid, three windows, standing SPX calls at every event,
cash/forward information, and target VIX call strips in THEOREM.md. The
parameter range remains every real `0≤ε<1/30`. No budget, conditional price,
joint claim, or additional vanilla constraint is added to the panel.

## Broader class

Permit any finite nonempty raw state space, any real probability weights, and
any filtration satisfying `FiniteModel` on the same integer event grid. Require
the same positive discounted SPX, `S0=S1=1`, full unnormalized martingale,
diagonal and tower equations, nonnegative additive conditional budgets, and
the same idealized VIX definition with exact tenor three. Require root budget
zero for cell zero and `c/2` for each of the six risky cells, where
`c=log(4/3)`. Retain the common pointwise moment envelope `Γ²<M` from THEOREM.md,
now applied to the actual stock and budget coordinates of the broader model.

There is no prescribed active/frozen transition kernel, no independent-sign
assumption, no schedule coordinate, no early-revelation rule, and no fixed
state cardinality in this decision class. Different witness representations
are allowed because the class explicitly permits every finite state space.
Zero-probability histories remain harmless unnormalized equations.

A finite compatible law in this class would disprove persistence of this
panel's incompatibility once the early-revealed architecture is removed. It
would also be a finite-event compatible law in a class allowing arbitrary
state spaces. It would not be a continuous-path realization theorem. A negative
result confined to finite states would be labelled accordingly; no arbitrary
LP grid can establish a broader impossibility.

## First constructive search, not a decision procedure

Try a subclass with six active/frozen cells and independent fair return signs,
but keep the schedule hidden. Add signals `Y1,Y2,Y3∈{0,1,2,3}` revealed only at
events 2, 3 and 4. At each fixing, the history consists of past activity bits,
past signs and all signals revealed so far. For joint schedule/signal weights,
impose the exact linear rows

`Σ_history p(a,y) (Wi(a)−Yi)=0`.

The signs are independent of schedule/signals. The standing prefix-count laws
give the required SPX strips; signal marginals give the prescribed VIX strips
only after the conditional-budget construction and its quote bridge are
proved. All 64 schedules and all 64 signal triples are initially included.
This is a search for a constructive witness inside the broad class, not a
claim that every broad model has this form. Infeasibility here would only reject
this search route.

Start at ε=0. If a compatible law is found, separately prove a mixture
construction with the uniform baseline, including the information revealed
about the mixture, to cover the entire same-panel family. Do not infer this
closure without a full conditional-model proof.

## Completion obligations

Deliver an exact admissible law or a sound broader contradiction, full Lean
verification of the entire new claim, unchanged quote definitions, an
independent statement audit, and updated status/verification/manuscript files.
The existing publication is not to be silently strengthened or replaced.

## Result and exact statement

The constructive answer is **compatibility**. For every real `0≤ε≤1`, there
is a finite filtered law in `Broad.Admissible` fitting every standing SPX call
and all three target VIX call strips from THEOREM.md, with exactly the same
target definitions. In particular this covers every original parameter
`0≤ε<1/30`. The early-revealed impossibility and this broader existence are
consistent: they quantify over different, explicitly declared information
classes. This resolves the same-panel extension, not the general question
whether some other vanilla panel has an architecture-free triple obstruction.

The checked headline declarations are
`Extension.financial_same_panel_compatibility`, `Extension.same_panel_compatible`
and `Extension.information_restriction_is_essential` in
`formal/VixOverlap/ExtensionHeadline.lean`. The main existence theorem supplies
an actual `FiniteModel`; its type requires every martingale, diagonal and full
tower row. `Broad.Admissible` imposes the original initial conditions and the
pointwise moment bound on actual model coordinates. `Broad.FitsPanel` refers
to the same `stockCallPrice`, `vixCallPrice` and `QuoteContract.targetCall`
definitions used by the published theorem. Complete integration verification
passed on 2026-10-15: 27 modules freshly compiled, exit status 0, and 39 distinct
declarations audited with only the three accepted foundational axioms. See
VERIFICATION.md and `notes/extension-verification.log` for the full evidence.

## Exact zero-parameter witness

Take the 39 positive entries `(a,y,n)` listed in
`certificates/hidden-witness.json`, equivalently the literal vectors in
`HiddenData.lean`. The probability of each latent entry is `n/1024`; the
numerators sum to 1024. Append six independent fair signs. The raw space has
`39·64=2496` states and each raw state's probability is `n/65536`.

The stock recursion is unchanged:

`S0=S1=1`, `S(h+1)=Sh·(1+ah·ξh/2)`, `h=1,…,6`.

At events 0 and 1, this branch has trivial information. Event `j≥2` reveals
the activity bits and return signs for cells `h<j`, and signals `yi` with
`i+2≤j` (zero-based `i`). Signals are revealed at their VIX fixing, not earlier.
The full event history retains everything already revealed. No future sign
is revealed by a signal, because the entire sign vector is independent of
the schedule-and-signal pair.

For cell `h=1,…,6`, set

`C(j,h)=c E[ah | Hj]`, and `C(j,0)=0`.

The expectation here conditions on the latent history. Adding the independent
past signs does not change it. Formally `conditionalAverage` divides by the
history mass only when that mass is positive and is zero otherwise. All 39
latent weights are strictly positive, so every represented latent history has
positive mass. The complete model rows are nevertheless proved unnormalized.

The exact certificate proves:

1. `P(a1+…+aj=k)=choose(j,k)/2^j` for every prefix and count.
2. `P(yi=k)=μi(k)` for all three target signal laws.
3. For every fixing and full latent history, `ΣH p(Wi−yi)=0`.
4. Each activity bit has mean one half.

These are data facts checked by Lean over integers and then transferred to
real weighted sums. Python's rational checks and the numerical solver are
discovery aids only. All represented histories are checked by their
representatives; histories outside the carrier have zero probability.

## Why these data yield a financial law

Given the schedule-and-signal pair and the past signs, every unobserved sign
is still fair. The mean stock multiplier is therefore one even when the
activity bit is only partially known. This proves every stock martingale
row after summing over the latent history. Stock adaptation follows because
all past activity bits and signs are included in the history.

The fair-sign identity `E[−2 log(1+ah ξh/2) | a]=c ah` proves each diagonal
row after conditioning on the actual history. Conditional averaging over
refining equivalence classes proves every tower row. The finite averaging
lemma explicitly covers zero-mass histories. Nonnegativity and `C(j,h)≤c`
follow from `0≤ah≤1`. Root means give the required `c/2` budgets.

For window `i`, linearity and certificate item 3 give

`Σh∈window_i C(i+2,h)=c E[Wi | H(i+2)]=c yi`.

Consequently the model's own VIX equals `sqrt(c yi/3)`. Summing the conditional
log returns telescopes to the log return over the window, so the same budget
is exactly `−2 E[log(Sfinish/Sstart) | Hstart]`. This is the idealized
conditional-log VIX relation with tenor three.

The distribution of stock at event `j+1`, conditional on a schedule, depends
only on its prefix activity count. Certificate item 1 thus gives every
standing SPX call price, not merely selected strikes. The signal masses give
every target VIX call price. No particular joint law is inferred from quotes:
this is one compatible law supplied by construction.

The original bounds continue to hold pointwise: stock lies in
`[1/64,729/64]`, `|log S|≤6 log 2`, and every future budget is in `[0,c]`.
There are eight stock dates and 28 future-budget coordinates. Hence the
actual-coordinate `Γ` is at most the original `L`, and `Γ²<L²+1=M`.

## The full parameter family and information timing

Mix the hidden witness with weight `1−ε` and the original uniform-schedule
model with weight `ε`. Use their disjoint union as one fixed 6592-state
carrier for all parameters. The branch is hidden at event 0 and revealed at
event 1. Each branch then follows its own declared filtration. Both branches
have `S0=S1=1`, root budget zero in cell 0, and root budget `c/2` in every
risky cell, so the enlarged event-1 information preserves every root row.

At every positive event, an unnormalized conditional equation in the mixture
is the corresponding branch equation multiplied by its branch weight. This
also proves the equations when that weight is zero, at ε=0 or ε=1. No division
by `ε` or `1−ε` occurs. VIX is computed from the selected branch's budgets;
all unconditional call prices are the corresponding convex mixtures.
The SPX strips coincide in both branches, and VIX masses become exactly
`(1−ε)μi+εν`. Pointwise bounds are inherited branch by branch.

This construction retains the active/frozen stock kernel and independent
fair signs. It changes the permitted information about activity. The broader
decision class does not demand this kernel; using it for a compatible witness
is sufficient and imposes no restriction on the theorem's existence claim.
The carrier also includes fixing-time signals and a mixture branch. We do
not claim to obtain the witness merely by coarsening the original filtration
on its original 4096-state carrier. These additional latent states and signals
are expressly permitted by the broader contract frozen before the search.

## The mechanism and its limit

At latent entry 0, the activity schedule is `000000` but the first fixing
signal is 2. Entry 4 has schedule `000100`, the same first signal, and the
same already-revealed activity bit. Both weights are positive and the two
entries are indistinguishable at the first fixing, although their eventual
first-window activity counts differ. Thus `yi` is a conditional expectation,
not a realized count. The published separator applies to the three realized
counts under early revelation; it need not apply to these conditional means.

The result is model consistency, not an executable-arbitrage claim. It gives
a finite-event compatible law; no continuous-path or exchange-settlement
realization is asserted. The qualitative sensitivity to information is
already prior art. The scoped contribution is the exact resolution of this
particular all-strike panel, including its parameter family and full checked
financial construction.
