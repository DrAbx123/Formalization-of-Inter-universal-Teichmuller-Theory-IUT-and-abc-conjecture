# Task L memo: random matrix theory / free probability / quadratic Gauss sums vs the Θ-packet normalization

File: tmp/sheaf/xif/paper/_taskL/RMT_FREEPROB_GAUSS_MEMO.md
(The S735 prefix is shared by concurrent Lean tool files; this memo avoids that
namespace collision.)

Date: 2026-10-30
Status: research memo. No Lean theorem is claimed, no compilation is claimed, and
no surrogate object is proposed. Task L of the current xif paper batch.

## 0. Executive answer (three lines)

1. Quadratic Gauss sums give exact identities, but only phase/annihilation
   identities: for N = 2l, G(a) = sum_{j mod N} exp(2*pi*i*a*j^2/N) vanishes
   for odd a, and for even a = 2b with b not = 0 mod l has |G|^2 = 4l. The mu_{2l}-orbit
   average of every nonzero Θ label is exactly 0. None of these is a positive
   normalization of the Θ hull.
2. The only exact positive average identity of the packet is the geometric
   mean: prod_{j=1}^{l*} q[2u]^{j^2} = q[1u]^{(l^2-1)/48}, whose per-label
   value is q[1u]^{(l+1)/24}. This is the average-first scalar; it equals the
   q-pilot only at l = 23, and it makes the target false for l >= 29. It is
   not the paper hull log (S707, S716, S726).
3. The paper-order scalar is the hull extremum 1/(2l), i.e.
   -|log Θ| = (1/(2l)) * (-|log q|) in the q[2u] normalization. The target
   -|log Θ| >= -|log q| is then true with room; the remaining exact gap is
   the q[2u]/root-stack carrier (fractional scaling data / Haar
   normalization), not an average or a Gauss-sum identity. RMT and free
   probability do not supply that carrier identity.

## 1. The actual objects and the exact gap

Paper target (frozen, do not change):

    -|log Θ| >= -|log q|,   equivalently  |log Θ| <= |log q|.

Current formal objects:

* Θ packet: paper labels ThetaLabel = { j : SignedLabel // 0 < j.1 }, i.e.
  j = 1,...,l*, l* = (l-1)/2 (PaperC3ThetaRootActual.ThetaLabel).
  Paper value q[2u]^j^2 = q[1u]^{j^2/(2l)}, with mu_{2l} ambiguity
  (PAPER_THETA_NORMALIZATION_STATUS.md).
* Paper root coefficient: qVFamPaperRootCoefficient = order(q_v)/(2l) and
  qVFamPaperThetaTensorCoefficient j = j^2 * order(q_v)/(2l)
  (QVFamRootFactorCorrectionActual).
* Hull: rootThetaHull = closure (union_j F(j^2 c) * O_hol) in
  RootHullContainmentInequalityActual; the paper-coefficient hull is
  paperRootThetaHull with c = paperRootCoefficientFamily
  (BadPlacePaperRootThetaHullActual).
* Exact formula gap: PaperRootHullFormulaGap T b =
  ArithmeticTuplePureFractionalScalingData at coefficient order/(2l)
  plus paperRootThetaHull = F(order/(2l)) * O_hol; the formula scalar is
  paperRootThetaFormulaLog = -(order/(2l)) * log p.
* Root extension side: rootNormedElement, rootNormedThetaValueInL,
  rootImageRadius = p^{-c_norm/(2l)} (S709), and
  rootExtensionProductImageHullLog on the extension product
  (PaperRootExtensionThetaHullAuditActual).
* Completion obstruction: a completion generator of norm p^{-order/(2l)}
  is equivalent to a completion 2l-th root of q[1u], contradicted by S342.
  The paper q[2u] lives in the extension/root stack, not in the completion
  (PAPER_THETA_NORMALIZATION_STATUS.md, FROZEN_TARGET.md).

A usable "exact average/normalization identity" would have to do one of:

(i) compute the paper hull log (the normalized log of the actual hull) exactly;
(ii) construct the q[2u] fractional scaling data / Haar normalization on the
root-stack carrier and identify it with the paper hull log.

It is not enough to compute an average of point values, a Gauss sum, or a
model measure: those are different objects (S707, TARGET_STRENGTH_LEDGER).

## 2. The Θ packet: exact identities that do exist

Throughout, l >= 5 is an odd prime, N = 2l, l* = (l-1)/2,
zeta = exp(2*pi*i/N), and q = q[1u] in (0,1) for the numerical checks.
The script tmp/sheaf/xif/paper/_taskL/verify_identities.py reproduces the
table below.

### 2.1 The mu_{2l}-orbit

For a fixed nonzero label j (so 1 <= j <= l*), the orbit is

    { (zeta^m q[2u])^{j^2} : m in Z/2l } = q[2u]^{j^2} * mu_{2l}.

Two exact identities hold.

(O1) Orbit average is zero:

    (1/(2l)) * sum_{m=0}^{2l-1} (zeta^m q[2u])^{j^2}
      = q[2u]^{j^2} * (1/(2l)) * sum_m zeta^{m j^2} = 0,

because 2l does not divide j^2 for 0 < j < l (if 2l | j^2 then l | j,
contradiction). In particular, for every j in F_l^x the orbit average is
zero, not q[2u]^{j^2} and not a positive normalization.

(O2) Orbit modulus is invariant:

    |zeta^m q[2u]^{j^2}| = |q[2u]|^{j^2}   for every m,

so the log-volume (which depends only on the modulus) is unchanged by the
mu_{2l} action. The orbit product is

    prod_{m=0}^{2l-1} (zeta^m q[2u])^{j^2} = q[2u]^{2l j^2},

and its 2l-th root is q[2u]^{j^2}; this is again only the modulus.

Conclusion: the mu_{2l} indeterminacy is invisible to the log-volume and
annihilates value averages. It cannot supply a factor 2l, a positive
normalization, or a bridge to the hull log.

### 2.2 Quadratic Gauss sums

Define

    G(a) = sum_{j=0}^{N-1} exp(2*pi*i*a*j^2/N),   N = 2l.

The classical exact evaluation (standard quadratic Gauss sum; numerically
checked for l = 5,7,11,13,17,23,29) is:

* G(a) = 0 for every odd a;
* for a = 2b with b not = 0 mod l:

      G(2b) = 2 * G_l(b) = 2 * (b/l) * eps_l * sqrt(l),

  where (b/l) is the Legendre symbol and
  eps_l = 1 if l = 1 mod 4, eps_l = i if l = 3 mod 4.
  Hence |G(2b)|^2 = 4l.
* G(0) = 2l.

The exact L^2 count identity is also useful as a warning:

    sum_{a=0}^{N-1} |G(a)|^2 = N * #{(j,k) mod N : j^2 = k^2 mod N}
                             = 2l * (4l - 2) = 8l^2 - 4l,

not N^2 = 4l^2. The reason is that G is the Fourier transform of the
push-forward of the uniform measure under j -> j^2, not the DFT of the
Θ packet itself; DFT unitarity cannot be applied to G as if it were the DFT
of (q^{j^2})_j.

What the Gauss sums do not give:

* G(a) is a sum of phases. The Θ packet is positive real, q[2u]^{j^2}.
  Replacing the packet by a root of unity zeta^{a j^2} changes the object.
* The only occurrences of 2l are G(0) = 2l (the group order) and
  |G(2b)|^2/2 = 2l (a squared modulus/count). Both are additive log
  constants or counts, not a multiplicative factor in the exponent of q.
* There is no exact positive identity sum_j q^{j^2} = (some canonical
  normalization): for real q this is a finite Jacobi theta sum with no
  elementary closed form; only the modular transformation of the full
  sum_{j in Z} q^{j^2} exists, and it does not apply to F_l^x.

The closest "2l identity" is therefore

   2l = |G(2b)|^2 / 2      (b not = 0 mod l),

but inserting log(2l) into a log-volume is an additive correction, not a
multiplicative normalization of the exponent, and it depends on a choice of
frequency b and a Legendre phase. It is not the paper normalization.

### 2.3 The F_l^x / l* average identities

The paper labels are the l* positive representatives of the +- classes.
The exact sum-of-squares identity is

    sum_{j=1}^{l*} j^2 = l(l^2-1)/24,

hence the average-first exponent coefficient is

    (1/l*) * sum_{j=1}^{l*} j^2/(2l)
      = [l(l^2-1)/24] / [(l-1)/2 * 2l]
      = (l+1)/24.

Equivalently, the product and geometric mean are exact:

    prod_{j=1}^{l*} q[2u]^{j^2}
      = q[1u]^{(l^2-1)/48},
    (prod_{j=1}^{l*} q[2u]^{j^2})^{1/l*}
      = q[1u]^{(l+1)/24}.

This is the only exact positive "average/normalization identity" of the
packet. Its consequences:

* l = 23: coefficient 1; the geometric mean equals the q-pilot q[1u].
  (l = 7 is a different coincidence: the product, not the mean, is q[1u]^1.)
* l < 23: coefficient < 1; average-first is larger than the q-pilot.
* l > 23: coefficient > 1; average-first is smaller than the q-pilot.
  First failure at l = 29: (29+1)/24 = 5/4.

This identity is exact, but it is average-first. It is not the paper
hull log. The paper object is the hull of the union of possible images
(hull first), then the procession average; the S663 average-first signed hull
is explicitly proved not to be the paper hull log in S726
(PaperHullVsS663ThetaAverageGap is false).

### 2.4 The hull-extremum identity

For the current single-block carrier,

    rootThetaRegion j = F(j^2 c) * O_hol,   c = paperRootCoefficient >= 0.

Since F(c') decreases as c' increases and j^2 >= 1, every region is
contained in the j = +-1 region:

    F(j^2 c) * O_hol  subset  F(c) * O_hol.

Hence the union's hull is the extremal region, and the exact paper-order
coefficient is

    hull log = -c * log p = -(order/(2l)) * log p
             = (1/(2l)) * (q-pilot log),

i.e.

    -|log Θ|_hull = (1/(2l)) * (-|log q|),
    |log Θ|_hull   = |log q|/(2l) <= |log q|.

So the paper inequality is true with room under the hull-first reading. This
is the scalar that the current paperPerBThetaHullLog / rootNormHull route
uses (S716, S726, S729). The remaining gap is not the inequality; it is the
carrier that realizes c = order/(2l).

The ratio between the two exact scalars is the second moment of the label
distribution:

    ((l+1)/24) / (1/(2l)) = l(l+1)/12 = average of j^2.

This is the precise measure of what "average-first" does: it replaces the
hull extremum by the mean of j^2. No probabilistic identity can change this
ratio without changing the label measure.

### 2.5 Numeric table (exact rationals)

| l | l* | avg j^2 | average-first C=(l+1)/24 | product exponent P=(l^2-1)/48 | hull-first H=1/(2l) | C <= 1? |
|---|---|---|---|---|---|---|
| 5  | 2  | 5/2   | 1/4  | 1/2  | 1/10 | yes |
| 7  | 3  | 14/3  | 1/3  | 1    | 1/14 | yes |
| 11 | 5  | 11    | 1/2  | 5/2  | 1/22 | yes |
| 23 | 11 | 46    | 1    | 11   | 1/46 | yes (equality) |
| 29 | 14 | 145/2 | 5/4  | 35/2 | 1/58 | no |
| 37 | 18 | 703/6 | 19/12| 57/2 | 1/74 | no |

## 3. Random matrix theory: exact moments, wrong object

RMT exact identities are expectations over an ensemble, e.g. for GUE
E tr H^{2k} is a Catalan number (E tr H^2 = N^2), and for a Haar unitary
E |tr U^k|^2 = 1. They are exact, but they are moment identities of a
chosen probability measure/trace.

Why they do not transfer:

1. The Θ packet is a deterministic finite set in a p-adic (or complex model)
   carrier, not the spectrum of a random matrix. The paper average is a finite
   uniform average over ThetaLabel, not a trace or expectation.
2. Matching the paper's label second moment l(l+1)/12 requires choosing an
   ensemble variance. A semicircle with that variance reproduces the same
   average-first coefficient (l+1)/24 and hence the same l >= 29
   obstruction. Choosing a different variance (e.g. 2l) to make the target
   pass changes the measure and is a surrogate, not the paper normalization.
3. The finite mu_{2l}-orbit is the regular 2l-gon, not a Wigner ensemble;
   its empirical spectral measure is uniform on the circle, with moments
   delta_{2l | k}. The Θ exponent j^2 is not a moment order.
4. The paper quantity is a log-volume of a hull, not a moment. A moment
   identity controls sum_j theta_j or tr, while the hull log depends on the
   extremal region / Haar measure. AM-GM goes the wrong way: the log of an
   average is >= the average of logs, so a bound on sum_j theta_j cannot
   prove the required lower bound on the average of hull logs.

The only RMT-adjacent exact statement here is the Gauss-sum/DFT evaluation of
Section 2.2, which is phase-only.

## 4. Free probability: exact traces, wrong state

Free probability is a theory of a trace/state on a noncommutative algebra,
with free independence and free cumulants. The paper's label average is a
commutative finite average (a state on functions on a finite set); for
commutative algebras free independence coincides with classical independence,
and free cumulants reduce to classical cumulants.

Two concrete traps:

1. Variance substitution. The uniform label distribution on
   j = 1,...,l* has mean (l+1)/4 and variance

       Var(j) = E[j^2] - E[j]^2 = (l+1)(l-3)/48.

   The free second cumulant kappa_2 of a commutative distribution is its
   variance. Dividing Var(j) by 2l gives

       (l+1)(l-3)/(96 l),

   which is < 1 for all l >= 5 and would superficially satisfy the target.
   But the paper average uses E[j^2], not Var(j). The difference is
   E[j]^2 = (l+1)^2/16; dropping it is a change of normalization, not a
   free-probability theorem. Example: at l = 29, the correct average-first
   coefficient is 5/4, while the variance-substituted one is
   30*26/(96*29) = 65/232 ~ 0.28. The latter is a surrogate.

2. Haar state of mu_{2l}. If one models the mu_{2l} ambiguity by the
   Haar state on mu_{2l}, the moments are m_k = delta_{2l | k}. The only
   nonzero low-order value appears at order 2l, not at the Θ exponent j^2.
   The exponent average (1/l*) sum j^2/(2l) is not a moment/cumulant of
   this state, and the log-volume is not a trace.

Free-probability exact identities (semicircle moments, free CLT, cumulants)
are either tracial/asymptotic or belong to a different measure. They cannot
give an exact finite inequality for the paper's hull log. The "free" label is
misleading here: the problem is commutative and finite; there is no
noncommutative independence to exploit.

## 5. What a usable identity would have to be

The exact gap is the carrier, not the average. A paper-faithful normalization
identity would look like one of:

1. Extension fractional scaling data. Construct
   ArithmeticTuplePureFractionalScalingData at coefficient order/(2l) on
   the actual root extension L = K(root) (value group (1/(2l))Z, root
   rootNormedElement, norm p^{-order/(2l)}), not on the completion. This is
   the natural home of q[2u]; S342 shows the completion version is
   impossible.
2. Haar/log transport. Prove an exact identity between the extension
   product Haar/log (rootExtensionProductImageHullLog) and the paper hull
   log / paperRootThetaHullLog. The needed statement is a finite-extension
   Haar normalization identity (covolume/discriminant/degree), not an average
   over labels and not a Gauss sum. The exact transport is currently recorded
   as RootThetaToCompletionHullMapGap / the PaperRootHullFormulaGap
   carrier gap.
3. Label/Ind2 carrier. Decide whether the paper's "union of possible
   images" is taken in the single tensor block (where the j-regions are
   nested and the hull is the extremal j = +-1 region) or in the j-indexed
   product/procession (where the per-copy hulls average). The paper's (Ind2)
   label action and the product structure decide this. The current
   rootThetaHull unions over labels in one block, which is the hull-first
   reading; S726 confirms the paper hull log is not the S663 positive average.
   A proof that this is the paper's (Ind2) union is missing; an average
   identity cannot replace it.

Formal-state caveats (important before any carrier bridge):

* Label set. paperRootThetaHull calls rootThetaHull, whose union is over
  SignedLabel (this includes j = 0), not over ThetaLabel (0 < j). The
  j = 0 region is F(0) * O_hol = O_hol, the full unit ball. Let
  c = order/(2l). If c >= 1, F(c) * O_hol is strictly smaller than O_hol,
  so the claimed hull equality to the minimal j = +-1 region is false as a
  set equality. If 0 < c < 1, the discrete valuation gives
  F(c) * O_hol = O_hol as a set, so the set equality can hold, but the
  formula -c log p still fails: the completion has no element of norm
  p^{-c}, and the Haar log of O_hol is 0. In both cases the paper labels
  exclude 0 and the union must be over ThetaLabel, not SignedLabel
  (RootHullClosednessActual restricts to nonzero labels). The paper's
  fractional formula also needs the extension carrier; see S342.
  PAPER_OBJECT_SPEC.md and FULL_OBJECT_AUDIT.md already list this as
  required fix E1.
* PaperRootHullFormulaGap is completion-impossible (S342), not just
  unproved. Do not fill it with a completion generator or a Gauss-sum
  normalization.
* PaperHullVsS663ThetaAverageGap is false, not merely unproved (S726): the
  hull log is nonpositive, while the S663 positive magnitude average is
  strictly positive. The average-first object cannot be the paper hull.
* S705's (2l-1)/12 uses the full F_l^x representative set 1,...,l-1 (all positive
  representatives), not the paper's l* +- classes. The correct paper
  coefficient is (l+1)/24 (S694, S711); do not use (2l-1)/12.

## 6. Verdict table

| Direction | Exact identity? | Gives paper Θ hull log / q[2u] carrier? | Verdict |
|---|---|---|---|
| Quadratic Gauss sums | yes: odd a zero; G(2b) = 2(b/l) eps_l sqrt(l); abs(G(2b))^2 = 4l | no: phase/count only; 2l appears additively at best | reject as normalization |
| mu_{2l} orbit | yes: orbit average 0; modulus invariant; orbit product q^{2l j^2} | no: annihilation / no change of log-volume | reject |
| Product / geometric mean | yes: q^{(l^2-1)/48}, mean q^{(l+1)/24}; equals q-pilot at l = 23 | no: average-first; false target for l >= 29 | reject for paper; keep as diagnostic |
| Hull extremum | yes: 1/(2l), target true with room | this is the paper-order scalar; carrier formula still missing | use as scalar; carrier open |
| RMT moments | yes for chosen ensembles | no: wrong measure/trace; matching second moment reproduces obstruction; changing it is a surrogate | reject |
| Free probability | yes for traces/cumulants | no: commutative finite average; variance substitution is a surrogate; mu_{2l} moments are not j^2 | reject |

## 7. Recommendation

1. Do not use random matrix theory, free probability, or quadratic Gauss
   sums as a normalization of the Θ packet. They give exact phase/annihilation
   identities, not the paper hull log.
2. Keep the exact diagnostic pair:
   * average-first coefficient (l+1)/24 (product/geometric mean identity);
   * hull-first coefficient 1/(2l) (extremal region);
   * ratio l(l+1)/12 (second moment).
   This locates the gap in the hull/carrier, not in the arithmetic.
3. The next actionable step is carrier-level, outside this task's toolkit:
   construct the q[2u] fractional scaling data / Haar normalization on the
   root extension, or prove the extension-to-completion hull log transport.
   Keep PaperRootHullFormulaGap and RootThetaToCompletionHullMapGap as the
   exact open interfaces; do not replace them by an average or a Gauss sum.
4. Fix the label-set issue (ThetaLabel, 0 < j) before claiming the hull
   equality. This is independent of RMT/Gauss and is already listed in
   PAPER_OBJECT_SPEC.md / FULL_OBJECT_AUDIT.md.

## 8. Candidate Lean statements (NOT compiled, NOT asserted)

These are exact arithmetic statements only. They are recorded for a future
stage-2 statement file; none is claimed as proved here.

    -- product/geometric mean of the paper packet
    theorem packet_product_exponent (l : PrimeGeFive) :
      (∑ j in Finset.Icc 1 (lStar l.value),
          ((j : Real)^2) / (2 * l.value)) =
        (((l.value : Real)^2 - 1) / 48) := by
      sorry

    theorem packet_average_coefficient (l : PrimeGeFive) :
      (1 / (lStar l.value : Real)) *
        (∑ j in Finset.Icc 1 (lStar l.value),
          ((j : Real)^2) / (2 * l.value)) =
        ((l.value : Real) + 1) / 24 := by
      sorry

    theorem packet_threshold (l : PrimeGeFive) :
      ((l.value : Real) + 1) / 24 <= 1 ↔ l.value <= 23 := by
      sorry

    -- quadratic Gauss sum (needs a concrete primitive additive character;
    -- see S684/S689 for the finite tool file)
    theorem quadraticGaussSum_odd_eq_zero ... := by sorry
    theorem quadraticGaussSum_even_normSq ... :
      Complex.normSq (quadraticGaussSum l psi (2*b)) = 4*l := by sorry

    -- mu_{2l} orbit average (needs the concrete root of unity action)
    theorem mu2lOrbitAverage_eq_zero ... := by sorry

The first three are elementary real/rational identities (sum of squares).
The Gauss/mu_{2l} statements need a concrete primitive additive character
and the root-of-unity action; they are not in the current file and are not
asserted.

## 9. Reproducibility

Scripts (research only, no Lean):

* tmp/sheaf/xif/paper/_taskL/verify_identities.py — exact rational table,
  Gauss-sum numerical checks, mu_{2l} orbit averages, second-moment
  threshold.
* tmp/sheaf/xif/paper/_taskL/check_gauss_free.py — exact Gauss formula
  checks, mu_{2l} moments, label variance.

Commands run:

    python tmp/sheaf/xif/paper/_taskL/verify_identities.py
    python tmp/sheaf/xif/paper/_taskL/check_gauss_free.py

Both scripts use Python 3.13 / sympy 1.14.0 and print the tables quoted
above. The numerical Gauss checks are to 1e-13; the rational tables are exact.

## 10. References (repo and standard)

Repo:

* tmp/sheaf/xif/paper/TASK_LEDGER.md (canonical status; lines 82-95 exact
  missing, 104-112 invalid/superseded).
* PAPER_THETA_NORMALIZATION_STATUS.md (q[1u], q[2u], theta normalization,
  S342 completion obstruction).
* FROZEN_TARGET.md, TARGET_STRENGTH_LEDGER.md (frozen target; forbidden
  substitutions; q-pilot definition).
* S694ThetaAverageNormalizationActual.lean (l* labels, weight 1/l*).
* S703GlobalPaperThetaComparisonActual.lean,
  S704PaperThetaLogVolumeFormulaActual.lean (average coefficient and
  reduction to the coefficient inequality).
* S705QPilotThetaFormulaAuditActual.lean (per-label ratio; caution:
  (2l-1)/12 uses the wrong label set).
* S707ThetaHullVsThetaValueActual.lean (hull log vs theta value; pointwise
  ratio > 1 does not refute the hull comparison).
* S709RootImageRadiusFormulaActual.lean (root radius p^{-c/(2l)}).
* S711QNormalizationSearch.md (correct coefficient (l+1)/24, threshold
  l <= 23, normalization table).
* S716PaperThetaHullLogSourceAuditActual.lean,
  S726PaperHullVsS663GapActual.lean (paper hull log is the root hull log,
  not the S663 positive average; S726 is a negation).
* S719PaperRootHullGapDecompositionActual.lean,
  BadPlacePaperRootThetaHullActual.lean,
  RootNormalizedThetaHullActual.lean (gap decomposition: scaling data +
  hull set equality).
* RootHullContainmentInequalityActual.lean,
  RootHullClosednessActual.lean (hull over labels; nonzero-label
  restriction and closedness gap; the j = 0 issue).
* S689_GAUSS_ORBIT_MEMO.md, S684QuadraticGaussFiniteActual.lean (prior
  finite Gauss tool and candidate statements).
* PAPER_OBJECT_SPEC.md, FULL_OBJECT_AUDIT.md (ThetaLabel vs SignedLabel;
  required fixes).

Standard mathematics:

* B. C. Berndt, R. J. Evans, K. S. Williams, Gauss and Jacobi Sums,
  Wiley, 1998 (quadratic Gauss sums; exact evaluation).
* K. Ireland, M. Rosen, A Classical Introduction to Modern Number Theory,
  Springer GTM 84, Chapter 8 (quadratic Gauss sums).
* D. Mumford, Tata Lectures on Theta I, Birkhäuser, 1983 (theta functions,
  modular transformation; finite sums have no such transformation).
* A. Nica, R. Speicher, Lectures on the Combinatorics of Free Probability,
  Cambridge, 2006 (free cumulants; commutative case = classical cumulants).
* J. A. Mingo, R. Speicher, Free Probability and Random Matrices,
  Springer, 2017 (Haar unitary moments; RMT moment identities).
* G. W. Anderson, A. Guionnet, O. Zeitouni, An Introduction to Random
  Matrices, Cambridge, 2010 (GUE moments).

## 11. Final answer to Task L

Concrete identity offered: the exact geometric-mean identity

    (prod_{j=1}^{l*} q[2u]^{j^2})^{1/l*} = q[1u]^{(l+1)/24},

with threshold l = 23; together with the exact Gauss-sum evaluation
(G(odd) = 0, |G(2b)|^2 = 4l) and the exact mu_{2l} orbit annihilation.

Refusal: none of these is the paper Θ-pilot hull log. The paper-order
scalar is the hull extremum 1/(2l); the exact remaining gap is the
q[2u]/root-stack carrier (fractional scaling data / Haar normalization),
not an average, moment, or Gauss-sum normalization. RMT and free probability
do not supply that carrier identity; using them would change the measure or
the object, i.e. would be a surrogate. The only safe use of the average
identity is as a diagnostic: it shows precisely why the average-first reading
fails for l >= 29 and why the hull-first reading must be the paper's.
