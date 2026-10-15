# Independent verification record

The verifier independently read the four pinned TeX sections, compared the
Lean interfaces, reconstructed the implication chain, and challenged the
proposed generator. Primary integrated this record on 15 October 2026.
This document distinguishes written proofs from finite implementation tests.

## Exact source definitions

For x in {0,1}^n, x^B flips exactly the coordinates in B. Ordinary
sensitivity s(f,x) counts coordinates a for which f(x^{a}) != f(x), and
s(f)=max_x s(f,x). Block sensitivity bs(f,x) is the largest number of
pairwise disjoint nonempty blocks whose individual flips change f at x;
bs(f)=max_x bs(f,x). Zero-input block sensitivity is bs(f,0).

Fix d>=1, M>=3, L=d+2, k=2M²+1, r=ceil(sqrt M), t=16. A regular
tournament has outdegree M². Labels on i->j belong to its **head row j**.
A forbidden set has 16 vertices and one freely chosen m_j in [r] at each
vertex, satisfying a(i,j)=m_j for every internal directed edge. A vertex
with no incoming edge imposes no condition. The source's random existence
bound is k^16 r^-104 <= 3^16 M^-20 < 1.

At level l, H_l=d+1-l and N_l=LM(kr)^l. Partition the base coordinates
into M disjoint L-blocks E_j, with centers z_j=1_{E_j}. Put
D(x)=min_j dist(x,z_j), and P_{0,q}=1[D(x)<=d+1-q], q=1,...,d+1.

At recursive level l, put Q=H_{l-1}. Clause i for parent index q requires
P_{l-1,Q}(x_{i,c})=1 for every c=1,...,r and
P_{l-1,Q-q}(x_{j,a(i,j)})=0 for every i->j. The parent is their OR.
The indices are valid and each condition of a fixed clause uses a distinct
child. Increasing q strengthens gates; this preserves nesting. These are
total Boolean functions, without partial promises on inputs.

S_{l,b} is the maximum, over q and inputs with P_{l,q}(x)=b, of the number
of raw bits changing that predicate. J_{l,b} is the maximum over q<q'
and inputs where both predicates equal b, of bits a for which **both**
P_{l,q}(x^a) and P_{l,q'}(x^a) equal 1-b. The same input and same raw bit
must be used. Empty maxima are zero; in particular J_{d,0}=J_{d,1}=0.

## Initial profiles and disjoint witnesses

Distinct centers have distance 2L=2d+4. A rejecting input has at most one
center within distance d+1, so S_{0,0}<=d+1<=L. The source uses L.
S_{0,1}<=LM, and the singleton-radius predicate attains LM at a center.
The function D is 1-Lipschitz, so a single flip cannot cross two distinct
integer radii: both joint profiles are zero.

Every predicate rejects zero. At level l there are Mk^l disjoint nonempty
blocks, each of size Lr^l, whose individual flip at zero makes every
predicate accept. Inductively, copy a previous witness into all r children
of one row and take its union. That row's targets accept; other rows stay
zero and all outgoing gates pass. Different rows/family indices give
disjoint blocks. These witness blocks partition the N_l coordinates.
Their existence proves nonconstancy at every level.

## Published recurrences and quantitative step

Writing primes for the preceding level,

    S1 <= M² S0' + r S1'       J1 <= M² J0' + r S1'
    S0 <= 16 S0' + S1' + 3 J1'
    J0 <= 16 S0' + 3 J1'.

For rejection from a one, fix an initially accepting clause; every
sensitive bit must break it. Joint rejection fixes a clause accepting at
the stronger index; a gate failure crosses both child thresholds.

For acceptance from zero, fix the initial candidate lists T (exactly one
failed target, all gates pass) and G (exactly one failed gate, all targets
pass). Every successful bit repairs a clause in these lists. T is
head-coherent, so |T|<=15. The tournament on G has every outdegree<=1,
so |G|<=3 and at most one vertex with internal outdegree zero. All other
gate repairs cross both the weaker gate and strongest target thresholds.
For simultaneous parent acceptance even the exceptional repair crosses
two distinct child gate thresholds. Taking unions of possible raw bits
is legitimate; disjointness of clause supports is not assumed.

For M>=9^(d+1), normalize by M^{l+b}. With u_l=max_b S_{l,b}/M^{l+b},
v_l=max_b J_{l,b}/M^{l+b}, epsilon=max(r,16)/M<=2/3^{d+1}, obtain
u_l<=(1+epsilon)u_{l-1}+3v_{l-1} and
v_l<=epsilon u_{l-1}+3v_{l-1}. Starting from u_0<=L,v_0=0, comparison
sequences satisfy U_l<=2L and V_l<=epsilon L(3^l-1). Indeed summing
increments bounds U_l by L+epsilon L[3(3^l-1)/2-l]<2L for l<=d.
Thus S_{l,b}<=2LM^{l+b}.

## OR, amplification, growth, and dimension

OR M disjoint copies of P_{d,1}. Its dimension is n=LM²(kr)^d.
All copies reject zero, and their block witnesses give bs(f,0)>=M²k^d.
At a zero input, sensitivities add; at a one input with two accepting
copies no bit can reject the OR, and with one accepting copy its
sensitivity is at most S_{d,1}. Hence s(f)<=2LM^{d+1}, so
bs(f)/s(f)² >= 2^d/[4(d+2)²], which diverges with d.

More generally, OR c copies has n=cLM(kr)^d,
A=max(c S0_bound,S1_bound), B=cMk^d. For fixed profile bounds and
Mk^d>S0_bound, log(B)/log(A) increases up to c=S1_bound/S0_bound and
decreases afterward. The two neighboring positive integers suffice for
the optimal integer c. This is baseline optimization, not a new theorem.

For disjoint composition, s(f o g,x) equals the sum of s(g,x_i) over
outer sensitive coordinates i, so s(f o g)<=s(f)s(g). If g(0)=0,
Cartesian products of disjoint zero-sensitive blocks give
bs(f o g,0)>=bs(f,0)bs(g,0). They remain disjoint and nonempty.

At d=9,M>=9^10, set A=22M^10,B=M²k^9. Then B/A²>=128/121>1.
For alpha=log(B)/log(A)>2, m-fold iteration has dimension n^m, rejects
zero, and has s<=A^m and bs(0)>=B^m>=s^alpha. Thus bs grows unboundedly.
Also s grows unboundedly by the published universal bound bs<=s^4,
since the established lower bound on bs diverges.

## First-difference proof audit

For h-digit words and labels (first differing coordinate, source digit),
the verifier independently checked that every head-coherent set has size
at most h+2. A bucket sharing its first digit and containing an internal
edge has a head receiving a label with coordinate>1. Such a head must
dominate every outside vertex. Two nonsingleton buckets therefore cannot
coexist. Nor can two outside singleton buckets coexist with one large
bucket, because the edge between them would disagree with the incoming
source digit already imposed by the protected head. Induction on h,
with indegree<=1 giving the h=1 bound3, proves the theorem.

This verifies the infinite structural claim, not merely small examples.
The tournament may have arbitrary orientation. Query bit complexity is
conservatively O((log M)²) for fixed h using schoolbook division; constant
arithmetic-operation counts must not be described as constant bit time.
The verifier subsequently read saved CONSTRUCTOR.md and label_contract.py
in full. The compression by the rank of the source digit after omitting
the fixed head digit is injective at each head, so preserves exactly the
same coherent sets. Disjoint coordinate offsets preserve the coordinate
component. The h=13,q>=3 family, its q=3 arithmetic and q>=4 inequality,
mixed-radix optional examples, and last-radix-2 refinement all checked.
The code rejects reversed directed-edge calls and uses zero-based labels
consistently. No correctness defect was found. Constructor's bounded run
passed exhaustive orientation tests on 129,088 small tournaments; the
verifier did not rerun that test. The induction, not the tests, establishes
the infinite claim.

## Companion profile and final arithmetic audit

The verifier independently read saved PROFILE.md and accepted its final
six-branch S0 and five-branch J0 bounds. The essential points checked were:
all but at most one target repair crosses two child thresholds; G>=2
forces all target repairs to be joint; a source target's head label can
be reassigned when it has only the sole G incoming edge; and stronger-index
candidate lists cover all joint successes. A gate in those lists must
already fail at the weaker index, or the weaker parent would initially
accept. The local examples are not claimed to be full recursive towers.

The verifier also read recurrences.py, seed_certificate.py and MANUSCRIPT.md.
The source baseline uses the correct base profiles and immediate gate
envelope. All six/five new branches match the proof; min(J,S) capping is
valid. The fixed certificate uses certified intervals to choose between
the two optimal OR-copy candidates, and keeps the selected count unchanged
for the structural comparison. Thus B and n are identical, while the
integer sensitivity bound A decreases strictly.

Decimal.ln is correctly rounded; adjacent representable values enclose its
exact result. Positive directed division then encloses log(B)/log(A).
The certificate additionally verifies exact integer-power inequalities.
See the [official Decimal documentation](https://docs.python.org/3/library/decimal.html#decimal.Decimal.ln).
The optional research scan ranks candidates in binary floating point, so
its winner is only the best observed candidate, not a certified global
or sampled-domain optimum. The fixed final seed uses certified selection.
After the JSON was generated, the verifier checked its parameter values,
both exponent intervals, identical B and n, and exact A reduction without
rerunning the computation. The integrated reproduction command then passed
source hashes, both local checkers, and the certificate recomputation.

## Formalization scope and limits

Source inspection of the 51 cached sensitivity Lean files found no lexical
occurrences of sorry, axiom, native_decide, trustCompiler, or ofReduceBool.
Model.lean uses literal ordinary sensitivity and disjoint nonempty block
families. RecursiveProfiles.lean implements same-input/same-bit joint
maxima. Recursive.lean states recursive_four_recurrences with regularity,
GoodLabeling, nesting and r>0 hypotheses. ConstructedSeed.lean supplies
them; Separation.lean has no remaining combinatorial assumption.

No Lean elaboration, kernel replay, comparator run, or transitive axiom
audit has been performed here. Main.lean is an import aggregator, not an
independent certificate. The source's noncomputable/Classical conventions
give no efficient generator. Our new proof is a written mathematical proof
with independent review and executable checks; it is not Lean-formalized.
