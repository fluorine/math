# What already follows from the published formulas

These calculations are baseline analysis, not a novelty claim. They prevent
attributing an exponent improvement from parameter choice to a new theorem.

The manuscript's displayed quantitative choice M>=9^(d+1) and bound
A=2(d+2)M^(d+1) are convenient sufficient estimates, not necessary
restrictions for the full four-profile recurrence. The latter is valid for
all M>=3 with admissible labels and r=ceil(sqrt M).

We compare two source-derived baselines:

- `published`: iterate its displayed four inequalities exactly, starting
  S0=d+2, S1=(d+2)M, J0=J1=0.
- `immediate`: use the source proof's S0=d+1 base bound, |T|<=15, and the
  exact possibilities for the gate-list contribution, max(S1+J1,3J1).
  This still counts all target repairs by S0; it does not use the new
  target-joint invariant. Enforce the definitional J_b<=S_b in both modes.

For resulting bounds a,b on S0,S1 and c OR copies, A=max(ca,b),
B=c M k^d, n=c(d+2)M(kr)^d. In the separation regime Mk^d>a, the
exponent is increasing for c<=b/a and decreasing for c>=b/a. This follows
by differentiating log(c Mk^d)/log(max(ca,b)) on the two intervals;
the latter derivative has the sign of log(a/Mk^d)<0. Thus compare only
the two positive integers bracketing b/a. The checker does this using
exact profile arithmetic; floating point proposes candidates, and exact
integer powers/certified intervals validate the reported exponent bounds.

The bounded scan in checks/baseline-scan.json covered d=1,...,24,
M=3,...,10000, and a sparse 5-percent geometric grid through 10^12.
The best observed exponents **on that grid** were approximately 2.01369653
for the displayed system and 2.01541075 for its immediate refinements.
Scan ranking uses floating point, so it does not certify an optimum even
over the sampled domain. Nor is it a global optimum: ceil(sqrt M), integer OR
balancing, and unsampled parameters can improve the sampled values.
No claim of best possible ordinary-sensitivity exponent is made.

In particular, an exponent exceeding 2.0154 is already obtainable from
the existing argument. Proving a new deterministic label generator makes
such a seed succinct but does not make that numerical exponent itself a
new separation theorem. The structural comparison must instead use the
same actual seed (same d,M,r,c, labels and dimension) and establish a
strictly smaller sensitivity bound, or a genuinely better admissible
regime. The final seed certificate supplies that comparison separately.

Both certificate calculations use only the no-coherent-16 contract. For
the final q=1001 seed, seven leading digits are common and k<q^6, so our
label theorem also gives a coherent-set bound of eight. That additional
label-specific consequence is unused in both calculations. The baseline
here therefore compares the two profile analyses at a fixed contract;
it is not the strongest elementary analysis of the explicit labels.

Re-run the optional bounded baseline scan from the topic directory:

```sh
python3 checks/recurrences.py --scan --output checks/baseline-scan.json
```

This is one serial CPU process, with a 60-second CPU limit and a 70-second
wall alarm. It does not instantiate a tournament, Boolean cube, or seed
truth table. The normal reproduction command validates a fixed result
and does not repeat this research scan.
