# W4 memo: Gauss sum / second moment / character sums versus the least lambda-O hull log

Status: research memo plus compiled Lean tools. No paper target is changed, no
surrogate object is introduced, no inequality is assumed.

Lean file: tmp/sheaf/xif/paper/W4GaussSecondMomentNoGoActual.lean
Compilation: lake env lean tmp/sheaf/xif/paper/W4GaussSecondMomentNoGoActual.lean
exits 0 in the current tree (transient Mathlib-olean read failures were retried;
the successful run is the recorded one).

## 0. Answer in one page

Question W4: can the exact Task L identities (mu_{2l}-orbit average zero,
quadratic Gauss sums, and the label second moment (l+1)/24) be used to identify
the normalized Haar log of the least lambda-O hull, or to prove that the l*
label average equals that hull log?

Answer: NO for the equality, and the exact identification that does exist is
the hull-extremum formula, not a Fourier/moment identity.

1. The least lambda-O hull is already computed: S793 proves
   paperLeastLambdaOHull = paperLambdaORegion(cRoot),
   cRoot_i = order(q_v)/(2l), i.e. the j = 1 (and j = -1) region.  The hull is
   an extremum (minimum coefficient), not an average.
2. With the pure fractional scaling datum D (the current exact carrier gap),
   S799 gives the normalized log exactly:
   paperLeastLambdaOHullLog = -sum_i cRoot_i * log p = paperQPilotLogLeast.
   This is the positive identification.  It uses no Gauss sum, no orbit average,
   and no second moment.
3. The l* average is exactly the second-moment coefficient:
   (1/l*) sum_{j=1}^{l*} j^2/(2l) = (l+1)/24.
   The Lean theorem w4ThetaLabelAverage_eq proves this, and
   paperThetaLabelAverage_rootThetaMagnitudeValue_eq proves that the actual
   l*-label average of the root theta magnitudes is order * (l+1)/24 * log p.
4. The hull coefficient is 1/(2l).  For l >= 5,
   1/(2l) < (l+1)/24, with ratio l(l+1)/12 = average of j^2 > 1.
   Hence the signed l* average log is strictly smaller than the least-hull log:
   paperThetaAverageLog < paperLeastLambdaOHullLog (under D, order > 0,
   log p > 0).  Equality is false, not merely unproved.
5. The mu_{2l}-orbit average of every nonzero label is exactly zero
   (stackMuRoot_orbitAverage_eq_zero).  A zero phase average cannot equal the
   strictly negative hull log.  Gauss sums are phase/count identities
   (G(odd)=0, |G(2b)|^2 = 4l, G(0)=2l); they contain no positive volume
   normalization of the hull.
6. RMT/free-probability moments are exact for a chosen ensemble/trace, not for
   the paper's finite l* average.  Matching the paper second moment forces the
   same (l+1)/24 and the same obstruction; changing the variance to make the
   target pass is a surrogate.

Conclusion: W4 is a no-go for the hoped-for Gauss/RMT identification.  The only
usable exact scalar is the hull extremum 1/(2l); the remaining exact gap is the
q[2u]/root-stack carrier (ArithmeticTuplePureFractionalScalingData and the Haar
transport), not a label average or a Gauss sum.

## 1. Exact objects and hypotheses

Paper labels: PaperThetaLabel l = Fin (l*), l* = (l-1)/2, positive
representatives j = 1,...,l*.  Weight 1/l* (S694).

Paper theta exponent: j^2/(2l) (IUT I Example 3.2(iv), IUT II Remark 4.7.3).
Root coefficient: qVFamPaperRootCoefficient = order(q_v)/(2l)
(QVFamRootFactorCorrectionActual).

Least lambda-O hull: S793:
  paperLeastLambdaOHull = paperLambdaORegion (paperRootCoefficientFamily),
where paperRootCoefficientFamily is constant order/(2l).  In particular the
hull is the minimal (j = 1) fractional-lattice region.

Hull log formula: S799.  For
  D : ArithmeticTuplePureFractionalScalingData
        (qVFamTensorPlaces T b) qVFamTensorTuple
        (paperRootCoefficientFamily T b),
  paperLeastLambdaOHullLog = -sum_i cRoot_i * log p = paperQPilotLogLeast.

This D is the exact carrier gap already recorded in TASK_LEDGER (paper hull
equality/Haar normalization).  W4 does not fill it and does not assume it
silently: every comparison theorem below takes D as an explicit hypothesis and
is labelled _of_data.

## 2. The exact second moment (Task L, now compiled)

For l* = (l-1)/2:

  sum_{j=1}^{l*} j^2 = l(l^2-1)/24,
  (1/l*) sum_{j=1}^{l*} j^2/(2l) = (l+1)/24.

Lean:
* sum_sq_paperThetaLabel
* w4ThetaLabelAverage_eq
* paperThetaLabelAverage_rootThetaMagnitudeValue_eq
* paperThetaAverageLog_eq_neg_rootThetaMagnitudeAverage

The last theorem identifies the S764 scalar paperThetaAverageLog with minus the
actual l*-label average of rootThetaMagnitudeValue:

  paperThetaAverageLog = - (1/l*) sum_i rootThetaMagnitudeValue(i)
                       = - order * (l+1)/24 * log p.

The arithmetic is unconditional.  No Gauss sum is needed for it.

## 3. Positive exact identification: the hull log is the extremum

Lean: paperLeastLambdaOHullLog_eq_leastFormula_of_data.

  paperLeastLambdaOHullLog = paperQPilotLogLeast
                           = - (order/(2l)) * log p

under D.  Equivalently, the hull log is the j = 1 region log.  This is the
paper-order scalar; it is the only exact positive identification available in
the current tree for the least hull.

This is an extremum statement.  It is not an average over labels, and no
character sum enters its proof.  The proof only uses:
* S793: the least hull equals the minimal region;
* S799: the normalized log of a fractional-lattice times holomorphic lattice is
  -sum c_i log p;
* the scaling datum D.

## 4. No-go I: every weighted average is at least the hull minimum

Lean: w4HullMin_le_weightedAverage and
      w4HullMin_lt_weightedAverage_of_pos.

For any probability weights w_i >= 0, sum w_i = 1:

  sum_i w_i * (j_i^2/(2l)) >= 1/(2l),

with strict inequality as soon as w puts positive mass on a label with j > 1.
Proof: each exponent is at least 1/(2l); the nonzero-label exponent is strictly
larger; the weighted sum is a convex combination.

The uniform l* average has w_i = 1/l* > 0 and includes j = 2,...,l*.  Hence

  1/(2l) < (l+1)/24

for every l >= 5 (S764; Lean w4HullMin_lt_average).  Numerically:
l=5: 1/10 vs 1/4; l=23: 1/46 vs 1; l=29: 1/58 vs 5/4.

Thus no probability average of the label exponents can equal the hull minimum
unless all mass is concentrated on j = 1.  A Gauss sum or a moment is such an
average (or a phase-weighted version); it cannot produce the extremum for the
uniform paper weights.

This is the structural reason W4 is a no-go, independent of any estimate.

## 5. No-go II: the l* average log is strictly below the hull log

Lean:
* paperThetaAverageLog_lt_paperQPilotLogLeast
* paperThetaAverageLog_lt_paperLeastLambdaOHullLog_of_data
* paperThetaAverageLog_ne_paperLeastLambdaOHullLog_of_data
* rootThetaMagnitudeAverage_lt_leastHullLog_of_data

For order(q_v) > 0 and log p > 0, and under D:

  paperThetaAverageLog < paperLeastLambdaOHullLog.

Reason: both are negative multiples of order * log p; the average coefficient
(l+1)/24 is strictly larger than the hull coefficient 1/(2l), so the average
log is more negative.  The actual-magnitude form is

  - (1/l*) sum_i rootThetaMagnitudeValue(i)
      < paperLeastLambdaOHullLog.

This is an exact strict separation, not an inequality that could be reversed by
a better Gauss estimate.  In particular the paper's l* average cannot be the
hull log.

Sign check: the hull log is negative, the average is even more negative.  The
ratio of magnitudes is l(l+1)/12 = E[j^2].

## 6. No-go III: mu_{2l}-orbit annihilation

Lean: stackMuRoot_orbitAverage_eq_zero.

For the actual finite root stack, let zeta = stackMuRoot, a primitive 2l-th
root in rootNormedAmbient.  For every 0 < j < l and every q:

  sum_{m=0}^{2l-1} ((zeta^m * q)^{j^2}) = 0.

Reason: 2l does not divide j^2 (if it did, the prime l would divide j,
contradicting 0 < j < l), so the geometric sum over the orbit vanishes.  The
general geometric lemma is orbit_sum_eq_zero; the divisibility lemma is
twoL_not_dvd_sq; primitivity is stackMuRoot_isPrimitive.

Interpretation:
* The orbit average is a phase/annihilation identity of value 0.
* The hull log is a negative real volume, strictly negative under order > 0 and
  log p > 0 (Lean paperQPilotLogLeast_neg).
* Zero cannot equal a negative volume.  The mu_{2l} ambiguity is invisible to
  the log-volume (the modulus is invariant), and its value average is zero.
* Orbit product: prod_m (zeta^m q)^{j^2} = q^{2l j^2}; its 2l-th root is
  q^{j^2}, which is again only the modulus, not a positive normalization.

So the orbit identity is real and exact, but it is the wrong sign/object.

## 7. Quadratic Gauss sums: phase and count, not hull volume

Task L (S689_GAUSS_ORBIT_MEMO.md) and S684 record the standard exact
evaluation.  For N = 2l, zeta = exp(2*pi*i/N),
G(a) = sum_{j mod N} zeta^{a j^2}:

* G(0) = 2l;
* G(a) = 0 for every odd a;
* for a = 2b with b not 0 mod l:
  G(2b) = 2 (b/l) eps_l sqrt(l), hence |G(2b)|^2 = 4l, where (b/l) is the
  Legendre symbol and eps_l = 1 or i according to l mod 4;
* the L^2 count is sum_a |G(a)|^2 = 2l(4l-2), not (2l)^2.

The full evaluation is a standard Gauss-sum theorem; W4 Lean does not formalize
it (S684 only has the trivial zero-frequency and even-symmetry lemmas).  This
is stated explicitly rather than faked.

Why it cannot identify the hull log:
* G(a) is a sum of phases; the paper theta packet is positive real at each
  label.  The exact Gauss evaluation is support/phase information.
* The only occurrence of 2l is additive (G(0)=2l) or a squared modulus/count
  (4l); inserting log(2l) into a log-volume is an additive correction, not the
  multiplicative exponent 1/(2l).
* The Gauss sum is not the DFT of the theta packet (q^{j^2})_j; it is the DFT
  of the push-forward of the uniform measure under j -> j^2.  DFT unitarity
  does not apply to the theta values.
* A character sum could in principle isolate the single label j=1 (the
  minimizer), but that is just the trivial extremal projection; it does not
  produce a new normalization and does not use the second moment.  The hull is
  already the j=1 region by S793.

## 8. RMT and free probability: exact moments, wrong state

Task L memo, Section 3-4, records the following; it remains correct.

* GUE moments E tr H^{2k} are Catalan numbers; Haar-unitary moments
  E |tr U^k|^2 = 1.  They are exact expectations for a chosen ensemble/trace.
* The paper l* average is a finite uniform average over PaperThetaLabel, not a
  trace and not an expectation over a random matrix.
* Matching the paper label second moment E[j^2] = l(l+1)/12 requires choosing
  an ensemble variance.  A semicircle with that variance reproduces the same
  average coefficient (l+1)/24 and hence the same l >= 29 obstruction.  Any
  other variance is a change of measure, i.e. a surrogate.
* The variance substitution (l+1)(l-3)/(96l) < 1 is not the paper average; at
  l=29 it is 65/232, while the correct average coefficient is 5/4.
* Free probability on a commutative finite label set reduces to classical
  probability; the mu_{2l} Haar state has moments delta_{2l | k}, not the
  j^2 moment used by the paper.

No RMT or free-probability identity supplies the q[2u] carrier or the hull
extremum.

## 9. What a positive construction would have to be

The exact gap is not the scalar.  A usable construction would have to do one of:

1. Supply the pure fractional scaling datum
   ArithmeticTuplePureFractionalScalingData at coefficient order/(2l) on the
   actual root extension L = K(root) (not the completion; the completion version
   is impossible by S342).
2. Prove the extension product Haar/log transport identifying the paper hull
   log with the extension hull log (covolume/discriminant/degree identity).
3. Prove that the paper's union of possible images is taken in the single
   tensor block (hull-first, j = 1 extremum) rather than in a j-indexed
   product/procession.  S793/S799 already formalize the hull-first object; the
   label action/(Ind2) remains the paper-identification question.

None of these is a Gauss sum, an orbit average, or a second moment.  A Fourier
identity can compute an average; it cannot replace the carrier or the hull
extremum.

## 10. Lean inventory

File: tmp/sheaf/xif/paper/W4GaussSecondMomentNoGoActual.lean

Arithmetic and second moment:
* sum_range_sq_succ
* lStar_two_mul_add_one
* sum_sq_paperThetaLabel
* w4ThetaLabelAverage_eq
* w4HullMin_lt_average
* paperThetaLabelAverage_rootThetaMagnitudeValue_eq
* paperThetaAverageLog_eq_neg_rootThetaMagnitudeAverage

Weighted-average no-go:
* w4HullMin_le_weightedAverage
* w4HullMin_lt_weightedAverage_of_pos

Orbit/Gauss-type identity:
* orbit_sum_eq_zero
* twoL_not_dvd_sq
* stackMuRoot_isPrimitive
* stackMuRoot_orbitAverage_eq_zero

Hull log versus average:
* paperThetaHullMinLog_eq_leastFormula
* paperLeastLambdaOHullLog_eq_leastFormula_of_data
* paperQPilotLogLeast_neg
* paperThetaAverageLog_lt_paperQPilotLogLeast
* paperThetaAverageLog_lt_paperLeastLambdaOHullLog_of_data
* paperThetaAverageLog_ne_paperLeastLambdaOHullLog_of_data
* rootThetaMagnitudeAverage_lt_leastHullLog_of_data

Verification:
* lake env lean on the file exits 0.
* No sorry, admit, axiom, or native_decide in the file.
* #print axioms on the audited main theorems (w4ThetaLabelAverage_eq,
  w4HullMin_lt_weightedAverage_of_pos, stackMuRoot_orbitAverage_eq_zero,
  paperLeastLambdaOHullLog_eq_leastFormula_of_data,
  paperThetaAverageLog_eq_neg_rootThetaMagnitudeAverage,
  paperThetaAverageLog_lt_paperLeastLambdaOHullLog_of_data) reports exactly
  propext, Classical.choice, Quot.sound (the allowed three).  The final
  corollary rootThetaMagnitudeAverage_lt_leastHullLog_of_data is a rewrite from
  the last audited theorem; a repeat #print axioms probe after it was added was
  blocked by transient Mathlib/Std olean read failures in the shared build tree,
  so that individual audit is marked not rerun, not claimed.
* The Gauss-sum full evaluation and RMT moment formulas are quoted from Task L
  and standard references; they are not formalized in this file.  The no-go
  does not depend on them.

## 11. Side audit (important for integration)

Two current-tree issues were found while building W4.  They are independent of
the W4 mathematics and should be handled by the integration owner.

1. S704PaperThetaLogVolumeFormulaActual.lean does not compile against the
   current tree.  Direct lake env lean reports stale proof failures at
   lines 82 and 101 (Finset.sum_congr application and mul_le_mul_right usage).
   W4 therefore does not import S704; w4ThetaExponent is the same j^2/(2l)
   formula, defined locally.

2. There are two definitionally equal native place selections:
   LeanFormal.IUT.nativePlaceSelection (HodgeTheater
   SourceDefinition31NativeContractBridgeReduction.lean) and
   N8Closure.nativePlaceSelection (NativeSourceReductionActual.lean).
   Opening both makes unqualified nativePlaceSelection ambiguous.  A direct
   rebuild of S764ThetaHullMinVsAverageActual.lean fails at its line 80 for this
   reason (qVFamily expects the N8Closure selection while the theorem type uses
   the LeanFormal.IUT one).  W4 pins every b to
   Bad (LeanFormal.IUT.nativePlaceSelection T), uses qVFamily at that b (which
   is accepted definitionally), and does not open N8Closure; it compiles in the
   current tree.  But consumers that rebuild S764/S799 may need a canonical
   alias or one definition removed before a full build.

## 12. Verdict table

Direction | Exact identity? | Identifies least hull log? | Verdict
---|---|---|---
mu_{2l} orbit average | yes: zero for every nonzero label | no: zero is not the negative hull volume | reject as normalization
Quadratic Gauss sum | yes: G(odd)=0, |G(2b)|^2=4l | no: phase/count; no exponent 1/(2l) | reject as normalization
l* second moment | yes: (1/l*) sum j^2/(2l) = (l+1)/24 | no: strictly above hull minimum | reject for equality; keep as diagnostic
Hull extremum | yes: 1/(2l), hull log = -order/(2l) log p under D | yes, this is the paper scalar; carrier D still open | use
RMT moments | yes for chosen ensemble | no: wrong measure/trace; matching variance reproduces obstruction | reject
Free probability | yes for chosen state | no: commutative finite average; wrong moments | reject

## 13. Recommendation

1. Do not pursue Gauss sums, mu_{2l} averages, RMT or free probability as a
   normalization/identification of the least lambda-O hull log.
2. Use the exact pair as a diagnostic:
   hull coefficient 1/(2l); l* average coefficient (l+1)/24;
   ratio l(l+1)/12.
3. The next actionable step is carrier-level: construct the pure fractional
   scaling datum / Haar transport on the actual root extension, or prove the
   paper-identification of the hull-first union.  W4 has removed the
   average/Gauss route with an exact strict separation.
