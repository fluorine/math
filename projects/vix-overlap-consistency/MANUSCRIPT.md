# Pairwise calibration and a three-window obstruction in a finite, early-revealed activity model

**Status: the integrated financial theorem and the clean Lean verification have passed.** The one-command verification exited with status 0 after freshly compiling all 19 local modules. See [VERIFICATION.md](VERIFICATION.md) for the pinned environment and verification record. This manuscript states the checked theorem for the finite architecture below. Novelty remains provisional, and the unrestricted SPX/VIX consistency problem remains unresolved.

## Scope and economic mechanism

Can ordinary marginal SPX and VIX call panels be compatible for every pair of three overlapping windows, yet incompatible jointly? We address this question in one explicit finite market. The six dates on which returns may be risky are announced before any of those returns is realized. The unknown schedule law determines dependence between activity at different dates; independent fair signs determine subsequent return directions.

This early revelation is a material restriction. It reduces the consistency problem to a finite marginal problem while retaining a positive discounted-stock martingale, a specified filtration, full conditional variance-budget equations, and ordinary option observations. The general common-budget framework, pairwise overlap inequalities, and the phenomenon of pairwise marginal compatibility without global compatibility are prior art. The proposed contribution is the particular vanilla-option embedding, its common-class witnesses, and its exact parameterized obstruction.

## One structural class

Events are \(0,1,\ldots,7\), one time unit apart. A schedule is \(a=(a_1,\ldots,a_6)\in\{0,1\}^6\). The class permits **every real probability vector**

\[
p:\{0,1\}^6\longrightarrow\mathbb R,
\qquad p(a)\geq0,
\qquad\sum_a p(a)=1.
\]

There is no rationality or probability-grid restriction. Independently of \(a\), draw six fair signs \(\xi_h\in\{-1,1\}\). Every law uses the same 4,096 labelled states \((a,\xi)\), with weight \(p(a)/64\); zero weights are permitted. The class contains no additional latent coordinates or additional information states.

At event 0 information is trivial. Event 1 reveals the entire schedule. At event \(j\geq1\), the available information is exactly the schedule and signs \(1,\ldots,j-1\). Each sign is revealed at the end of its cell, even if that cell is inactive. The discounted stock starts at \(S_0=S_1=1\) and satisfies

\[
S_{h+1}=S_h\left(1+\frac{a_h\xi_h}{2}\right),
\qquad h=1,\ldots,6.
\]

Thus an active multiplier is \(1/2\) or \(3/2\), and an inactive multiplier is 1. Conditional on the full history, each future sign remains fair. In particular, \(S\) is positive and is a martingale; every ordinary SPX forward has value 1.

Write \(c=-\log(3/4)=\log(4/3)>0\). Use integrated cell budgets, rather than annualized rates. Cell 0 has zero budget. For future cells \(h=1,\ldots,6\), set

\[
C(0,h)=c\sum_a p(a)a_h,
\qquad C(j,h)=c a_h\quad(1\leq j\leq h).
\]

These budgets are nonnegative and adapted. The identities

\[
\frac12\cdot\frac12+\frac12\cdot\frac32=1,
\qquad
\frac12\log(1/2)+\frac12\log(3/2)=-\frac c2
\]

supply the martingale and diagonal equations. For every full-history atom \(H\) at event \(j\), with raw-state weight \(q\) and mass \(q(H)\), the structural rows are

\[
\sum_{\omega\in H}q_\omega S_k(\omega)=S_j(H)q(H)
\quad(j\leq k),
\]

\[
\sum_{\omega\in H}q_\omega
   [-2\log(S_{h+1}(\omega)/S_h(\omega))]
   =C(h,h;H)q(H)
\quad(j=h),
\]

\[
\sum_{\omega\in H}q_\omega C(k,h;\omega)
   =C(j,h;H)q(H)
\quad(j\leq k\leq h).
\]

The Lean construction proves these rows from the sign law, including the reveal event and cell 0. It never divides by a history probability. A zero-mass history gives \(0=0\). Interval budgets are additive because they sum the same cell budgets at a fixed conditioning date; logarithmic telescoping also gives the corresponding full-window conditional identity.

The three windows are \([2,5]\), \([3,6]\), and \([4,7]\), all of tenor 3 and all containing the cell \([4,5]\). With one-based window indices,

\[
W_1=a_2+a_3+a_4,\qquad
W_2=a_3+a_4+a_5,\qquad
W_3=a_4+a_5+a_6.
\]

Their integrated budgets are \(cW_i\), so the idealized conditional-log-variance VIX variables are exactly

\[
V_i^2=\frac{cW_i}{3},\qquad V_i=\sqrt{\frac{cW_i}{3}}.
\]

VIX is expressed in volatility units; index points would add a factor of 100. No exchange-settlement or continuous-martingale realization is asserted.

The support and bounds are fixed for the entire class:

\[
\frac1{64}\leq S_j\leq\frac{729}{64},\qquad
|\log S_j|\leq6\log2,\qquad0\leq C(j,h)\leq c.
\]

For example, define

\[
\Gamma=1+\sum_{j=0}^7(|\log S_j|+S_j)
          +\sum_{0\leq j\leq h\leq6}C(j,h),
\quad
L=1+8(6\log2+729/64)+28c.
\]

The common bound is \(\Gamma^2<L^2+1\), pointwise, for every schedule law. Removing a quote constraint changes none of these bounds, transitions, states, or filtration rules. The uniform schedule law gives a nonzero-variance admissible example: every raw state has mass \(1/4096\), and each future risky cell has root budget \(c/2>0\).

## The observable panel and theorem statement

Fix all nonnegative-strike SPX calls at every event to their values under the uniform schedule law \(u(a)=1/64\). Cash has value 1. Each designated window contributes only its nonnegative-strike marginal VIX call strip. No schedule-contingent contract, budget, conditional price, count digital, or joint-dispersion claim is observed.

On count values \(n=0,1,2,3\), put

\[
\nu=\frac{(1,3,3,1)}8,\qquad
\mu_1=\frac{(3,3,9,1)}{16},\qquad
\mu_2=\frac{(1,15,15,1)}{32},\qquad
\mu_3=\frac{(1,46,1,16)}{64},
\]

and \(\mu_i^\varepsilon=(1-\varepsilon)\mu_i+\varepsilon\nu\). The target call price at strike \(K\geq0\) is

\[
C_i^\varepsilon(K)=\sum_{n=0}^3\mu_i^\varepsilon(n)
  \left(\sqrt{cn/3}-K\right)^+.
\]

**Finite-architecture statement.** For every real \(0\leq\varepsilon<1/30\):

1. For every proper subset \(J\subsetneq\{1,2,3\}\), there is a schedule law in the fixed class whose actual filtered model matches the standing SPX panel and every target VIX strip indexed by \(J\).
2. No real probability vector on the same 64 schedules matches the standing SPX panel and all three target VIX strips.
3. The supplied witnesses all have the same root budgets \(C(0,h)=c/2\), the common bounds above, and every structural conditional row. If \(\varepsilon>0\), every raw state in each supplied witness has strictly positive probability.

The empty subpanel is harmlessly included in the formal statement; in particular, all three singleton and all three pair subpanels are feasible. Deleting any designated window restores feasibility within this class. No global minimality across market classes, support sizes, or quote counts is claimed.

## Why ordinary calls determine the required statistics

Let \(N_k=a_1+\cdots+a_k\), with \(N_0=0\). At event \(k+1\), a stock value has the form \(3^u/2^n\), where \(n=N_k\) and \(u\) counts active upward signs. If

\[
\frac{3^u}{2^n}=\frac{3^v}{2^m},
\]

cross multiplication and unique prime factorization at the prime 2 give \(n=m\). This exact argument is formalized for natural exponents; it uses no rounded logarithms. Thus \(N_k\) is constant on each stock-price fiber in the declared architecture. Finite-support call inversion identifies the expectation of its atom indicators from the ordinary SPX call strip. The standing SPX panel consequently forces

\[
\mathbb P(N_k=n)=2^{-k}\binom{k}{n}
\qquad(0\leq k\leq6).
\]

Conversely, the uniform sign average of any stock payoff depends on a schedule only through \(N_k\). A permutation of the fair sign coordinates proves this assertion. The prefix-count marginals therefore reproduce all standing SPX calls, without selecting a distinguished coupling of those marginals.

The four values \(\sqrt{cn/3}\) are distinct because \(c>0\). Nonnegative-strike VIX calls identify their masses; cash normalization identifies the possible zero atom. The formal inversion uses finite call combinations to isolate positive support atoms. These arguments derive count marginals from ordinary quotes within the fixed class. They do not add digital instruments to the panel or establish that the same quotes force an arbitrary market into this architecture.

The prefix laws also imply \(\mathbb E[a_h]=1/2\), by subtracting consecutive prefix expectations. Hence every calibrating schedule law, not merely the chosen witnesses, has the same root budgets \(c/2\). The root budgets are consequences of the standing SPX panel, rather than extra observed constraints.

## Exact witnesses and the higher-order separator

[The exact certificate](certificates/exact.json) lists three integer vectors \(m^{12},m^{13},m^{23}\), indexed in binary order from \(000000\) to \(111111\). Each sums to 64. Let

\[
q^{ij}(a)=\frac{m^{ij}(a)}{64},\qquad
p_\varepsilon^{ij}(a)=(1-\varepsilon)q^{ij}(a)+\frac\varepsilon{64}.
\]

These formulas specify the witnesses completely; their raw-state weights are \(((1-\varepsilon)m^{ij}(a)+\varepsilon)/4096\). The integer checks establish every prefix marginal and both designated window marginals for each pair. The proved expectation identities then establish the same facts for every real \(\varepsilon\), with probability validity for \(0\leq\varepsilon\leq1\). Each singleton or empty subpanel uses any containing pair witness. The checked construction of the filtered model applies to these weights without changing its support or information rules.

Define the schedule statistic

\[
F=2\mathbf1_{W_1=0}-\mathbf1_{W_1=3}
 -2\mathbf1_{W_2=0}-\mathbf1_{W_2=3}
 -2\mathbf1_{W_3=0}+2\mathbf1_{W_3=3}.
\]

The finite certificate verifies \(F(a)\leq\sum_{k=3}^6r_k(N_k(a))\) at every one of the 64 schedules, with the following coefficient rows. Entries are indexed by the count \(n=0,\ldots,k\).

| Prefix \(k\) | \(r_k(0),\ldots,r_k(k)\) |
|---|---|
| 3 | \(2,2,2,0\) |
| 4 | \(5,3,1,1,0\) |
| 5 | \(-3,-1,1,1,1,0\) |
| 6 | \(-6,-4,-4,-4,-2,-2,0\) |

Taking expectation under any nonnegative **real** weighting with the standing prefix marginals gives the exact inequality

\[
2\mathbb P(W_1=0)-\mathbb P(W_1=3)
-2\mathbb P(W_2=0)-\mathbb P(W_2=3)
-2\mathbb P(W_3=0)+2\mathbb P(W_3=3)
\leq\frac{21}{32}.
\]

The unperturbed targets give \(22/32\), while the common uniform target gives \(-8/32\). Therefore the prescribed mixed panel has value

\[
\frac{22-30\varepsilon}{32}
=\frac{21}{32}+\frac{1-30\varepsilon}{32}.
\]

The last term is positive throughout the asserted parameter range. This is a universal contradiction for all schedule probabilities allowed by the class, rather than infeasibility on a probability grid. The kernel checks the finite arithmetic and the theorem taking the pointwise inequality to expectations; no linear-program optimum or external solver result is assumed. Logarithms and square roots remain exact real expressions in the financial bridge.

The obstruction concerns simultaneous frequencies of overlapping fully inactive and fully active runs. Each pair witness uses a different unobserved dependence between schedule bits while preserving all standing SPX marginals. One common law must respect the displayed inequality. Sharpness of the upper bound, novelty of a general marginal-polytope inequality, and robustness to arbitrary quote perturbations are not claimed. The proved robustness is the explicit mixture family and its quantified margin.

## The frozen local and pairwise tests

The tests specified before search are unchanged. Actual pair witnesses give admissible marginal calls, positive SPX, unit SPX forwards, the common bounds, and same-class singleton and pair feasibility. The count means satisfy

\[
\sum_n\mu_i^\varepsilon(n)n=\frac32,
\qquad
\mathbb E[V_i^2]=\frac c2
=-\frac23\mathbb E\left[\log\frac{S_{t_i+3}}{S_{t_i}}\right],
\quad t_i=i+1.
\]

The overlap bounds are proved for all strikes, with no sampled-strike argument or claim about unverified numerical maxima. For \(i<j\), the outgoing count is \(O_{ij}=\sum_{h=i+1}^{j}a_h\), and pointwise

\[
W_i\leq W_j+O_{ij},\qquad
(W_i-x)^+\leq(W_j-x)^++O_{ij}.
\]

The standing prefix marginals give \(\mathbb E[O_{ij}]=(j-i)/2\). Thus, for every \(0\leq\varepsilon\leq1\) and every real \(x\),

\[
\sum_n\mu_i^\varepsilon(n)(n-x)^+
-\sum_n\mu_j^\varepsilon(n)(n-x)^+
\leq\frac{j-i}{2}.
\]

The same proof permits any nonnegative count scale. At scale \(c/3\), for every real \(K\), it gives the prescribed VIX-squared certification inequality

\[
\mathbb E[(V_i^2-K)^+]-\mathbb E[(V_j^2-K)^+]
\leq\frac{c(j-i)}6
=-\frac23\mathbb E[\log S_{t_j}-\log S_{t_i}].
\]

In particular it includes all \(K\geq0\) required by the frozen test. The two VIX expectations denote the respective target marginal laws; the SPX log expectation is fixed by the standing SPX panel. No common triple law is being presumed in this notation.

## Formal proof components and remaining verification

The integrated declaration is `VixOverlap.financial_three_window_obstruction` in [Headline.lean](formal/VixOverlap/Headline.lean). Its existential witnesses are finite schedule laws \(p\); `ScheduleModel.model p` constructs the corresponding `FiniteModel`. That construction discharges the positive-stock, filtration, adaptation, martingale, diagonal, and full-history tower fields from the stated transition and information rules.

The proof components are:

| Mathematical obligation | Formal declaration or module |
|---|---|
| Fixed schedules, sign law, and conditional stock construction | `ScheduleData`, `CoinProduct`, `ScheduleStock`, `ScheduleModel.model` |
| Exact witnesses, universal separator, and mixture margin | `ScheduleCertificate.three_window_count_obstruction` |
| Root cell means forced by the standing marginals | `ScheduleCertificate.prefix_marginals_bit_mean` |
| Ordinary calls identify stock and VIX count statistics | `Vanilla`, `PriceIdentification`, `QuoteBridge` |
| Full-window unnormalized log relation | `ScheduleModel.model_window_log_identity` |
| Common support and moment envelope | `ScheduleBounds`, `ScheduleModel.uniform_moment_bound` |
| Forward, log, and VIX second-moment relations | `ScheduleMoments` |
| All-strike overlap tests and exact target means | `PairTests.mixed_overlap`, `PairTests.vix_squared_overlap`, `PairTests.mean_count`, `PairTests.vix_squared_mean` |

The clean verification command, `scripts/verify.sh`, exited with status 0 after freshly compiling all 19 local modules. All 22 audited declarations report exactly `propext`, `Classical.choice`, and `Quot.sound`; the full conditional model, ordinary-call bridge, separator, and pair tests are included in the checked development. The exact JSON-to-Lean data check also passed. Full statements and axiom output are recorded in [notes/verification.log](notes/verification.log). Exact toolchain and dependency pins, the build command, exit status, and statement-audit findings are maintained in [VERIFICATION.md](VERIFICATION.md). The novelty assessment remains separate from proof verification.

## Novelty and financial interpretation

The provisional literature review reports **no matching public resolution found as of 2026-10-15**. Its sources, versions, overlap analysis, and access limitations are recorded in [NOVELTY.md](NOVELTY.md). In particular, the latest SSRN version was not independently verified, and X coverage was limited to search-index results. This is a bounded search result, not proof of novelty.

Because the schedule is revealed early, the separator is a finite marginal-compatibility obstruction. It does not establish a new information-revelation or tower obstruction. The scope of any novelty claim must remain the explicit ordinary-SPX/VIX construction, its fixed-class proper-subpanel laws, and the particular exact family, subject to further literature scrutiny.

The result is a model-consistency statement. No self-financing trading strategy or executable arbitrage has been represented or proved. A fitted pair law is not identified uniquely by its marginal quotes. The same vanilla panel may admit a model outside the early-revealed architecture: proving that it does not would require a separate argument over a larger class. No unrestricted continuous-state impossibility, exchange-settlement theorem, or continuous realization is claimed.
