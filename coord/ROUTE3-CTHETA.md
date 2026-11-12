# ROUTE3-CTHETA — C-Theta / C-Phase: theta special values, algebraic comparison, mu2l phases

Task: task-92, R29l-stepxi. Read-only audit + constructible Lean draft.
Snapshot: 2026-11-13T04:19:03+08:00 Asia/Shanghai (task time).
Source: HANDOFF updated 2026-11-13, sections 6.5-6.6, 8.2 P5, 9.4.

## 0. Verdict

C-Theta is PARTIAL: the actual analytic odd-theta shift law is available and
gives a genuine multiplicative-shift analog of (C7). The general elliptic-point
translation theta(Z + P)theta(Z - P)/theta(Z)^2, the identification with
x(Z)-x(P), and the constant c_{P,v} in (C8)/(C9) are NOT available: there is no
line bundle/theta section/trivialization or general point-to-theta evaluation in
the tree.

C-Phase is INSUFFICIENT in the existing synchronized orbit: paperRootThetaMuOrbit
uses one primitive mu2l root and one exponent m for all labels, whereas IUT II
Remark 2.5.1(iii) makes the mu2l indeterminacies independent for different j.
Single-value statements only need the orbit; products/ratios need an equivariant
family or a 2l-th power, and the latter scales the readout by 2l.

Route 3 is retained as a conditional route, but the C-Theta gate is not passed
and no Cor. 3.12 comparison is claimed.

## 1. Actual shift law and reusable theorems

Files and exact declarations:

### 1.1 OddThetaShift
File: LeanFormal/IUT/Foundations/Theta/OddThetaShift.lean.
- oddTheta_shift at line 14:
  oddTheta q (r ^ a * U) =
    oddThetaSign a * r ^ (-(a ^ 2)) * U ^ (-(2 * a)) * oddTheta q U,
  under r^2 = q, r != 0, U != 0, ‖q‖ < 1, a : Int.
  This is the actual EtTh Proposition 1.4(ii) shift law used by this file.

### 1.2 OddThetaNormalization
File: LeanFormal/IUT/Foundations/Theta/OddThetaNormalization.lean.
- oddThetaSign_mul_i_zpow_neg_two_mul at line 14: the i-factor in the shift law
  at U=i is one.
- oddThetaFraction_eval at line 29:
  oddTheta q (i * r^j) / oddTheta q i = r ^ (-(j^2)),
  conditional on hi : i^2 = -1 and hTheta : oddTheta q i != 0.
- oddThetaFraction_eval_unconditional at line 45: the same normalized value
  with the nonvanishing supplied by the file's unconditional theorem.

### 1.3 OddThetaShiftSum
File: LeanFormal/IUT/Foundations/Theta/OddThetaShiftSum.lean.
- tsum_addRight_eq_tsum / tsum_const_mul_addRight_eq: integer reindexing.
- summable_oddThetaTerm_addRight: translated two-sided summability.
- oddTheta_shift_tsum_of_pointwise: the summation form of the shift law.
These are proof tools for the shift law; they do not create a curve theta
section.

### 1.4 ThetaFunctionLineBundleActual: actual values, no line bundle
File: tmp/sheaf/xif/paper/ThetaFunctionLineBundleActual.lean.
- Header lines 1-45: actual q_v^(j^2) values and zero locus; explicitly states
  that the theta line bundle, theta object A_Theta, theta function/global section,
  and identification with the {q_j^2} divisor are NOT available.
- ActualQThetaValueData at line 111; actualQThetaValueData at line 120;
  pow_eq j : value j = qUnit^(gaussExponent j.1).
- actualQThetaValueZeroLocus_empty at line 141: the q^j^2 values are nonzero;
  this is not the source theta divisor.

### 1.5 Root theta objects
Files: tmp/sheaf/xif/paper/PaperC3ThetaRootActual.lean,
PaperC3RootThetaHullActual.lean, PaperC3ThetaValuesActual.lean.
- paperRootThetaUnit at PaperC3ThetaRootActual:61-72;
  paperRootThetaUnit^(2l) = unitToAlgClosed(qUnit)^(j^2).
- ThetaLabel / paperRootThetaImagePointTheta at lines 82-116.
- paperRootThetaMuPoint at PaperC3RootThetaHullActual:46;
  paperRootThetaMuOrbit at :52; paperRootThetaHull at :59.
- paperQParameterMu2lOrbit at PaperC3ThetaValuesActual:78.

## 2. (C7): theta(Z+P) theta(Z-P) / theta(Z)^2

Target in HANDOFF 6.5 lines 948-971: a ratio of theta values at translated
points; if theta is a section of L = O_E([O]), the numerator is a section of
tau_P^*L ⊗ tau_{-P}^*L ⊗ L^{-2}, and one needs a trivialization or exact period
cancellation.

### 2.1 What is constructible

The actual analytic odd theta has a multiplicative variable U, not an additive
elliptic point. The constructible identity is the multiplicative-shift analog:
for q, r, U with r^2=q, r != 0, U != 0, ‖q‖<1, and a : Int,

  theta(r^a U) * theta(r^(-a) U) = (r^(-(a^2)))^2 * theta(U)^2.

Equivalently, when theta(U) != 0,

  theta(r^a U) * theta(r^(-a) U) / theta(U)^2 = (r^(-(a^2)))^2.

The U-period factors U^(-2a) and U^(2a) cancel exactly; the theta signs
oddThetaSign a and oddThetaSign(-a) multiply to 1. The remaining factor
(r^(-(a^2)))^2 is independent of U.

Lean draft: tmp/sheaf/xif/paper/Mzk1CThetaComparisonActual.lean, with
oddTheta_shiftProductSigned, oddTheta_shiftProduct, oddTheta_shiftRatio.
Watchdog status: see section 6; no manual lake/lean command was run.

### 2.2 What is NOT constructed

- theta is not constructed as a section of a line bundle on E;
  ThetaFunctionLineBundleActual header lines 1-45 says the line bundle/global
  section are missing.
- The translation Z+P is not available: the only proven shift is multiplication
  U -> r^a U (OddThetaShift:14); there is no theorem identifying an arbitrary
  elliptic point P with such a multiplicative shift.
- Consequently the target theta(Z+P)theta(Z-P)/theta(Z)^2 is not stated or
  proved. The multiplicative analog is a real identity, but it is not C7.
- No trivialization/period comparison for tau_P^*L⊗tau_{-P}^*L⊗L^{-2} is built.

## 3. (C8)/(C9) and the constant c_{P,v}

HANDOFF 6.5 lines 975-994: if F_{P,v} has the same divisor as x(Z)-x(P),
then F_{P,v} = c_{P,v}(x(Z)-x(P)) with nonzero c; C9 divides by F_{P,v}(W).

Current status:
- No actual F_{P,v} is constructed as a theta/line-bundle section on the curve.
- No identification of the divisor of a theta ratio with [P]+[-P]-2[O].
- c_{P,v} is unidentified. The multiplicative-shift ratio above has a
  computable constant (r^(-(a^2)))^2, but it is not identified with c_{P,v} and
  does not compare to x(Z)-x(P).
- C9 is therefore not available; even its numerator/denominator ratio is not
  a ratio of the target x-coordinate functions.

The existing SourceQlThetaLineBundleFromCurve.lean records six missing
line-bundle/theta data (file lines 24-31, 155-184); that is the exact asset gap.

## 4. C-Phase: independent mu2l phases (IUT II Remark 2.5.1(iii))

Paper: papers/motizuki_corpus/text/Inter-universal Teichmuller Theory II.txt,
Remark 2.5.1(iii), lines 4322-4343: the mu2l indeterminacies for different j
are independent; they are not synchronized to a single phase.

### 4.1 Existing orbit is synchronized

- paperRootThetaMuPoint (PaperC3RootThetaHullActual:46) is
    fun v => zeta_v^m * paperRootThetaUnit j v
  with the SAME primitiveMu2lRoot zeta_v and the SAME exponent m for every j.
- paperRootThetaMuOrbit (:52) ranges m for a fixed j; paperRootThetaHull (:59)
  unions over j. The union of orbits is a set, not a product of independent
  phase choices.
- paperQParameterMu2lOrbit (PaperC3ThetaValuesActual:78) also uses one R for
  all j.
Thus the existing objects describe a diagonal/synchronized mu2l action, not
the independent per-label indeterminacy of Remark 2.5.1(iii).

### 4.2 Consequence for products/ratios

Suppose a candidate is G = prod_j theta_j^{a_j}, and independent phases send
theta_j -> zeta_j theta_j, zeta_j in mu2l. Then
  G -> (prod_j zeta_j^{a_j}) G.
Knowing sum_j a_j = 0 is NOT enough: for arbitrary independent zeta_j, the
product need not be one. The expression is invariant for all independent phases
only if each exponent a_j is 0 mod 2l (on the relevant nonzero labels), or if
the object is upgraded to an equivariant family tracking the zeta_j.

Options:
1. Equivariant treatment: construct a family of mu2l-torsors/phases indexed by
   labels and prove the comparison morphism is equivariant. This is the
   faithful route; no such family is currently constructed.
2. Take the 2l-th power: independent phases are killed because zeta^(2l)=1.
   The Lean draft proves the generic finite-product lemma
   independent_mu2l_phase_pow_twoL. This is algebraically valid but changes the
   readout: log-volume/degree must be multiplied by 2l, and HANDOFF 6.6 warns
   that this does not allow re-applying the original comparison to the new
   power object.

### 4.3 Is the existing paperRootThetaMuOrbit enough?

For a SINGLE theta value: yes, as a mu2l orbit; any choice differs by an
element of mu2l and the orbit captures all choices.
For a product/ratio with more than one independent label: no. The existing
single zeta^m action is synchronized; it cannot express independent zeta_j.
It is therefore insufficient for the C-Phase requirement unless the final
expression is proved invariant under the diagonal action and the source
independence is separately shown to collapse to the diagonal on the actual
object. No such theorem exists in the tree.

## 5. Route-three decision

- Keep route three as a conditional research route.
- C-Theta gate: PARTIAL. The actual shift law yields a genuine multiplicative
  analog of C7, but not the elliptic-point C7/C8/C9 comparison.
- C-Phase gate: OPEN. Existing synchronized orbit is insufficient for products;
  need equivariant phases or a documented 2l-power normalization.
- Do not claim a theta divisor/line-bundle comparison or a constant c_{P,v}.

## 6. Lean draft and build status

File: tmp/sheaf/xif/paper/Mzk1CThetaComparisonActual.lean.
Declarations:
- oddThetaSign_mul_neg;
- oddTheta_shiftProductSigned;
- oddTheta_shiftProduct;
- oddTheta_shiftRatio;
- independent_mu2l_phase_pow_twoL.

Watchdog result:
- START 2026-11-12T20:32:50.716Z (final attempt)
- DONE EXIT=0 2026-11-12T20:34:21.484Z (91s)
- olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/Mzk1CThetaComparisonActual.olean
  (size 209408 B, mtime 2026-11-12T20:34:20Z)
- Final #print axioms:
  oddTheta_shiftProduct, oddTheta_shiftRatio, independent_mu2l_phase_pow_twoL
  all depend only on [propext, Classical.choice, Quot.sound].
- The per-file log still contains the earlier failed calc attempt; the final
  DONE block is the decisive status.

## 7. Exact source locations

- HANDOFF 6.5 C7/C8/C9: D:/iut-audit-20261113/COR312-THREE-ROUTES-HANDOFF-20261113.md:948-994.
- HANDOFF 6.6 independent phases: same file:1002-1021.
- HANDOFF 8.2 P5: same file:1413-1420.
- HANDOFF 9.4: same file:1567-1585.
- IUT II Remark 2.5.1(iii): papers/motizuki_corpus/text/Inter-universal Teichmuller Theory II.txt:4322-4343.


## 8. P5-A: analytic oddTheta vs root-valued paper theta (task-117)

### 8.1 Proved normalization identity

File: tmp/sheaf/xif/paper/Mzk1P5ThetaBridgeActual.lean.
Using OddThetaNormalization.oddThetaFraction_eval:

  oddTheta q (i * r^j) / oddTheta q i = r^(-(j^2)),

hence, for r != 0,

  (oddTheta q (i * r^j) / oddTheta q i)^(-1) = r^(j^2).

This is exactly the q_v^(j^2) exponent shape of paperRootThetaUnit when the
analytic root r is identified with paper q_v. It is a conditional normalization
identity, not an identification of the two objects.

### 8.2 Minimal missing objects for the actual bridge

1. A map/identification from the analytic normed field L (OddThetaShift) to
   the algebraic closure of the p-adic completion (PaperC3ThetaRootActual).
   The analytic r and the paperRootThetaUnit root live in different fields.
2. A proof that the analytic root r corresponds to the actual q_v = q^(1/2l)
   used by paperRootThetaUnit; the current analytic theorem only assumes
   r^2=q and is independent of the paper root construction.
3. The theta function/line-bundle section: ThetaFunctionLineBundleActual
   explicitly states no line bundle, theta object, global section, or divisor
   identification.
4. Kummer class identification: Example36SourceThetaDivisor missing item (d)
   (lines 112-115) says the identification of Kummer classes with theta values
   and the actual etale theta function is not proved.
5. A label-indexed shift map for the C7 expression theta(Z+P)theta(Z-P); the
   existing shift law only covers multiplication U -> r^a U.
6. The constant/trivialization comparison for tau_P^*L tensor tau_{-P}^*L
   tensor L^{-2}; no line-bundle trivialization is available.

The conditional theorem is therefore at the normalization/exponent level only;
the object-level P5-A bridge remains BLOCKED.

### 8.3 Build evidence

- File: tmp/sheaf/xif/paper/Mzk1P5ThetaBridgeActual.lean.
- START 2026-11-12T21:20:26.747Z; DONE EXIT=0 2026-11-12T21:21:34.323Z (68s).
- olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/Mzk1P5ThetaBridgeActual.olean
  (size 36368 B, mtime 2026-11-12T21:21:33Z).
- #print axioms oddThetaFraction_inv_eq_pow: [propext, Classical.choice, Quot.sound];
  no sorryAx.
- This identity is the one analytic-to-exponent alignment available; it does not
  close the object-level analytic/root/Kummer bridge.

End of report.