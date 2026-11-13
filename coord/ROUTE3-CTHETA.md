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


### 8.4 Label-indexed analytic shift (P5-A follow-up)

File: tmp/sheaf/xif/paper/Mzk1P5LabelShiftActual.lean.
- thetaLabelExponent j = positive integer representative of ThetaLabel j;
- analyticThetaLabelPoint i r j = i * r^(thetaLabelExponent j);
- oddThetaFraction_eval_thetaLabel:
    oddTheta q (analyticThetaLabelPoint i r j) / oddTheta q i
      = r^(-(thetaLabelExponent j ^ 2));
- thetaLabelExponent_pos and thetaLabelExponent_injective.
Build: START 2026-11-12T21:24:20.577Z;
DONE EXIT=0 2026-11-12T21:25:19.728Z (59s);
olean size 62520 B, mtime 2026-11-12T21:25:18Z;
axioms for both theorems: [propext, Classical.choice, Quot.sound], no sorryAx.

This is the label-indexed normalization layer only; it does not construct the
analytic/root/Kummer/line-bundle bridge. It supplies the correct j-indexing for
the C7 missing label map.


### 8.5 task-120: two named inputs + conditional comparison

File: tmp/sheaf/xif/paper/Mzk1P5CompareActual.lean (header marks CONDITIONAL
(named inputs)).

Named input 1 (AnalyticRootMap): a ring map L -> R, an analytic root r, a
target root qRoot, and root_image : toRoot r = qRoot. No existence/construction
is asserted.

Named input 2 (ThetaValueComparison): a constant c and, for every ThetaLabel j,

  toRoot (r^(-(j^2))) = c * qRoot^(j^2).

Conditional theorem p5_compare_conditional:

  toRoot ( oddTheta q (i*r^j) / oddTheta q i )
    = c * qRoot^(j^2),

using the label-indexed analytic normalization and the named comparison. The
constant c is explicit; the exponent is exactly j^2 on both sides.

Status of the six previous gaps is now:
- localized into the two named inputs: analytic/root field map and the
  normalized comparison constant;
- still separate: (3) line-bundle section/trivialization, (4) Kummer class
  identification, (5) general C7 point shift/label map, (6) constant/trivialization
  comparison for tau_P^*L tensor tau_-P^*L tensor L^-2.
The two inputs are NOT constructed; no toy field, no fake bridge, no sorry/axiom.
The conditional theorem is conditional transport of the exponent equality, not
an unconditional analytic/root identification.

Build evidence:
- START 2026-11-12T21:27:04.150Z; DONE EXIT=0 2026-11-12T21:28:00.689Z (57s).
- olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/Mzk1P5CompareActual.olean
  (size 205432 B, mtime 2026-11-12T21:28:00Z).
- #print axioms p5_compare_conditional: [propext, Classical.choice, Quot.sound];
  no sorryAx.


### 8.6 task-121: P5AnalyticRootBridge (named structure)

File: tmp/sheaf/xif/paper/Mzk1P5BridgeIntegrationActual.lean (header:
CONDITIONAL (named structure)).

The implemented structure P5AnalyticRootBridge (L R l) has fields:
- toRoot : L ->+* R, r : L, qRoot : R^x;
- thetaUnit : ThetaLabel -> R^x;
- c : ThetaLabel -> R^x, phase : ThetaLabel -> R^x;
- phase_pow : phase j ^ (2*l) = 1;
- comparison : toRoot (r^(-(j^2))) = c_j * phase_j * thetaUnit_j.

The theorem p5_bridge_compare proves:
  toRoot (oddTheta q (i*r^j) / oddTheta q i)
    = c_j * phase_j * thetaUnit_j,
with the exponent and constants explicit.

Build evidence:
- final DONE EXIT=0 2026-11-12T21:43:11.127Z (53s);
- olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/Mzk1P5BridgeIntegrationActual.olean
  (size 208088 B, mtime 2026-11-12T21:43:10Z);
- no sorry/axiom in the green source (the per-file log retains earlier failed
  attempts and their temporary sorryAx lines from elaboration failures; the
  final DONE block is decisive).

Exact GAPS remaining in this integration:
- thetaUnit is an abstract named root-unit family; no theorem identifies it
  with the actual paperRootThetaUnit family of PaperC3RootThetaActual.  The
  intended instantiation is a named input, not constructed.
- phase_j is a named mu2l phase family with only phase_pow; it is not proved
  equal to a paperRootThetaMuPoint/primitiveMu2lRoot phase, and no relation to
  paperRootThetaMuOrbit is constructed.
- toRoot, r, qRoot and the constants c_j remain named inputs; no analytic/root
  field map or line-bundle/Kummer identification is constructed.
Thus the theorem is a conditional root-unit comparison at the named-structure
layer, not the actual IUT II Remark 2.5.1 dictionary.


### 8.7 task-123: instantiate thetaUnit/phase with actual paper objects

File: tmp/sheaf/xif/paper/Mzk1P5BridgeInstantiateActual.lean.

- paperPhaseUnit m j := Units.mk0 (primitiveMu2lRoot^m_j), the actual
  primitive-root phase; paperPhaseUnit_pow proves its (2l)-th power is one.
- paperPhaseUnit_mul_theta: paperPhaseUnit m j * paperRootThetaUnit j
  = paperRootThetaMuPoint m j (definitional).
- actualP5Bridge (toRoot r c m hcomparison) is P5AnalyticRootBridge with:
  qRoot := twoLthRootAt,
  thetaUnit := paperRootThetaUnit,
  phase := paperPhaseUnit m,
  c := c,
  comparison := hcomparison.
- actualP5Bridge_thetaUnit and actualP5Bridge_phase are rfl equalities.

Status: PENDING, not yet green. The latest watchdog attempt still fails in
paperPhaseUnit_pow (Units.mk0 coercion unfolding) and in the hcomparison
signature (a local thetaLabelExponent/labelExp elaboration collision with the
Nat-valued imported name).  No final green claim is made; the diagnostic is:
- paperPhaseUnit_pow: after Units.ext the goal is
  ↑(Units.mk0 z ^ (2*l)) = ↑1; need an explicit val_mk0/pow_mul rewrite.
- hcomparison: local labelExp must be used consistently and its Int-ness is not
  being inferred at all uses; negative zpow fails with Neg Nat.
The intended compression (thetaUnit/phase/phase_pow actual, only c_j/hcomparison
named) is structurally correct but this file is not yet accepted.


### 8.8 P5-A5: actual qRoot-root identity and reduced hcomparison

File: tmp/sheaf/xif/paper/Mzk1P5ThetaRootUnitActual.lean.

- paperRootThetaUnit_eq_twoLthRootAt_pow:
    paperRootThetaUnit j v0 = twoLthRootAt v0 ^ (gaussExponent j).toNat
  by rfl (qRoot := twoLthRootAt, unit factor 1).
- paperRootThetaUnit_pow_twoL_eq: the same qRoot power raised to 2l equals
  unitToAlgClosed(qUnit)^(j^2), using paperRootThetaUnit_pow_twoL.
- actualP5Bridge_qRoot_eq: the instantiated bridge's qRoot is twoLthRootAt.
- hcomparison_qRoot_iff: the hcomparison input can be rewritten from
  paperRootThetaUnit to qRoot^(j^2) with no new data.

Consequently the thetaUnit/phase/qRoot identification is actual; the named
input left is the analytic comparison c_j/hcomparison itself (plus the analytic
field map toRoot and r).

Build evidence (final):
- START 2026-11-12T22:06:32.977Z; DONE EXIT=0 2026-11-12T22:07:30.803Z (58s).
- olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/Mzk1P5ThetaRootUnitActual.olean
  (size 77952 B, mtime 2026-11-12T22:07:29Z).
- #print axioms for the four theorems: only [propext, Classical.choice, Quot.sound];
  no sorryAx.  (The per-file log retains earlier failed attempts with temporary
  sorryAx; the final DONE block is decisive.)


### 8.9 P5-A6: is c_j forced to 1?

Let B be actualP5Bridge (qRoot = twoLthRootAt, thetaUnit j =
paperRootThetaUnit j, phase_j = paperPhaseUnit m j).  A5 proved

  paperRootThetaUnit j = qRoot^(j^2)          (unit factor 1),
  B.qRoot = twoLthRootAt.

The comparison field is

  toRoot (r^(-(j^2))) = c_j * phase_j * paperRootThetaUnit j.

If one additionally imposes the named root-image equality

  toRoot r = qRoot,

then the left side is qRoot^(-(j^2)), so the comparison forces

  c_j * phase_j = qRoot^(-(2*j^2)).                    (CJ)

Consequences:
- c_j = 1 is NOT automatic; it is equivalent to
  phase_j = qRoot^(-(2*j^2)).
- phase_j lives in mu2l.  Therefore c_j = 1 with a mu2l phase is possible only
  if qRoot^(2*j^2) is a 2l-th root of unity.  For the actual qRoot =
  twoLthRootAt with nontrivial q (non-root-of-unity valuation), this fails;
  the q-scale cannot be absorbed by a mu2l phase.
- Thus c_j is a genuine normalization/scale input, not removable by choosing
  phase_j.  The best possible statement under root-image is (CJ), not c_j=1.

There is a further root-order obstruction: analytic r satisfies r^2=q,
while qRoot = q_v satisfies qRoot^(2l)=q (twoLthRootAt_pow).  If a q-preserving
map sends r to qRoot, then qRoot^2 = qRoot^(2l), i.e.
qRoot^(2(l-1)) = 1.  For l >= 5 this is a nontrivial root-of-unity condition,
not true for the actual q_v with nontrivial valuation.  The correct analytic
root image should rather be qRoot^l (because (qRoot^l)^2 = qRoot^(2l) = q);
then the left side is qRoot^(-(l*j^2)) and (CJ) becomes

  c_j * phase_j = qRoot^(-((l+1)*j^2)),

still not 1 in general.

Exact GAP: the paper comparison cannot be closed by setting c_j=1 or by a
mu2l phase choice alone.  A separate q-normalization/root-order identification
(including whether the analytic root maps to qRoot or qRoot^l) is required.
No new Lean theorem is claimed here; the precise algebraic consequences are
(CJ) and its qRoot^l variant.  File/line anchors:
- PaperC3ThetaRootActual:61-72 (paperRootThetaUnit definition);
- PaperC3ThetaRootActual:52-58 (twoLthRootAt_pow, qRoot^(2l)=qUnit);
- Mzk1P5ThetaRootUnitActual paperRootThetaUnit_eq_twoLthRootAt_pow;
- Mzk1P5BridgeInstantiateActual actualP5Bridge_qRoot_eq.


### 8.10 P5-A7: corrected root image r |-> qRoot^l and c_j formula

The previous named root image toRoot r = qRoot is inconsistent with the actual
root orders: analytic r satisfies r^2=q, while qRoot=twoLthRootAt satisfies
qRoot^(2l)=q.  The corrected named input is

  toRoot r = qRoot ^ l.value.

Then for n = thetaLabelExponent j ^ 2,

  toRoot (r^(-n)) = qRoot^(-(l*n)).

With the actual paper root unit paperRootThetaUnit j = qRoot^n (P5-A5), the
comparison

  toRoot (r^(-n)) = c_j * phase_j * paperRootThetaUnit j

forces the exact relation

  c_j * phase_j = qRoot^(-((l+1)*n)).                 (CJ-L)

Consequences:
- c_j = 1 is equivalent to phase_j = qRoot^(-((l+1)*n)); it is not automatic.
- Since phase_j is a 2l-th root of unity, c_j=1 is possible only if
  qRoot^((l+1)*n) is a 2l-th root of unity.  For actual qRoot=twoLthRootAt
  with nontrivial q this fails, so the q-scale cannot be absorbed by phase.
- Therefore no theorem c_j=1 is written; the correct theorem is (CJ-L).

File change: Mzk1P5CompareActual.lean AnalyticRootMap now has
  root_image : toRoot r = qRoot ^ l.value
(the structure gained the explicit l parameter).  Its conditional theorem is
unchanged except for the corrected named field.

Mzk1P5BridgeIntegrationActual's P5AnalyticRootBridge has qRoot as a unit and
no root_image field, so the corrected root choice is an additional named input
there; it is not constructed.  The exact gap is: provide a q-preserving
analytic/root map with root_image r |-> qRoot^l, or a named proof of the same.

Build status: CompareActual modification is GREEN:
- DONE EXIT=0 2026-11-12T22:12:49.004Z (63s);
- olean .lake/build/lib/lean/tmp/sheaf/xif/paper/Mzk1P5CompareActual.olean
  (size 222248 B, mtime 2026-11-12T22:12:48Z);
- #print axioms p5_compare_conditional: [propext, Classical.choice, Quot.sound];
  no sorryAx.
The root_image field is now toRoot r = qRoot^l; the conditional comparison
remains theorem-level.  BridgeIntegration still lacks a root_image field, so
the corrected root choice for the actual bridge remains the explicit GAP.


### 8.11 P5-A8: root_image field in P5AnalyticRootBridge

Mzk1P5BridgeIntegrationActual.P5AnalyticRootBridge now has the explicit field

  root_image : toRoot r = (qRoot : R) ^ l.value

and Mzk1P5BridgeInstantiateActual.actualP5Bridge takes this root choice as a
named argument hroot, setting qRoot := twoLthRootAt and root_image := hroot.
Mzk1P5ThetaRootUnitActual.actualP5Bridge_qRoot_eq was updated accordingly.

With this field, for n = thetaLabelExponent j ^ 2 and thetaUnit_j = qRoot^n,
the corrected bridge comparison gives

  c_j * phase_j = qRoot^(-((l+1)*n))        (CJ-L)

so c_j=1 is not asserted; it would require phase_j = qRoot^(-((l+1)*n)),
which a mu2l phase cannot supply for nontrivial qRoot.

Build status: GREEN for the field integration.
- Mzk1P5BridgeIntegrationActual: DONE EXIT=0 2026-11-12T22:15:35.707Z (66s);
  olean 232536 B.
- Mzk1P5BridgeInstantiateActual: DONE EXIT=0 2026-11-12T22:18:10.186Z (53s);
  olean 95744 B (root_image := hroot field added).
- Mzk1P5ThetaRootUnitActual: DONE EXIT=0 2026-11-12T22:19:31.372Z (57s);
  olean 81624 B.
The phase relation is recorded as the exact algebraic formula (CJ-L); no fake
c_j=1 theorem is added.  The corrected root choice is now an explicit named
field/argument, not an assumption hidden in the bridge.


### 8.12 packaged P5QNormalizationInput and actual sources

File: tmp/sheaf/xif/paper/Mzk1P5QNormalizationInputActual.lean.

Structure P5QNormalizationInput (L R l) has one field data :
P5AnalyticRootBridge L R l.  The bridge data contains:
- toRoot, r, qRoot, root_image : toRoot r = (qRoot)^l;
- thetaUnit, c_j, phase_j, phase_pow (phase_j^(2l)=1);
- comparison (the CJ-L form).

Theorem p5_bridge_compare_of_qNormalizationInput derives
p5_bridge_compare directly from the packaged structure.

Actual sources still required (NOT constructed):
1. Analytic field map: an actual ring map from the analytic oddTheta field L
   to the root field R, and an actual root r with r^2=q.  No such map is
   constructed in Mathlib/the tree.
2. Root choice: a proof root_image : toRoot r = qRoot^l, where qRoot is the
   actual twoLthRootAt/q_v.  This is the corrected order-compatible choice
   (not qRoot).  Its source is the q-preserving analytic/root normalization.
3. Phase family: an actual label-indexed mu2l phase family phase_j and
   phase_pow.  paperPhaseUnit gives one synchronized construction; independent
   per-label phases and their comparison to paperRootThetaMuOrbit are not
   constructed.
4. c_j and comparison (CJ-L): the analytic theta value/root-unit comparison
   itself.  It needs the Kummer class/line-bundle section identification
   (ThetaFunctionLineBundleActual missing; Example36SourceThetaDivisor (d));
   no etale theta guess is made.

Thus P5QNormalizationInput is only the explicit carrier of the remaining
inputs; it is not an unconditional dictionary and does not assert c_j=1.

Build status: GREEN.
- Mzk1P5RootChoiceOrderActual: DONE EXIT=0 2026-11-12T23:09:25.918Z (78s);
  olean 103912 B; axioms [propext, Quot.sound].
- Mzk1P5CJDerivedActual: DONE EXIT=0 2026-11-12T23:12:21.796Z (59s);
  olean 45664 B; final axioms [propext, Classical.choice, Quot.sound];
  no sorryAx.
root_pow_l_square and root_pow_one_order are both proved; c_eq_one_iff
is a theorem derived from phase_relation, not a structure field.


### 8.13 phase/qRoot relation file (P5 phase batch)

File: tmp/sheaf/xif/paper/Mzk1P5PhaseRelationActual.lean.

structure P5PhaseRelationData (R) (l):
- qRoot and qRoot_ne_zero;
- c_j and phase_j;
- phase_pow : phase_j^(2l)=1;
- relation : c_j * phase_j * qRoot^((l+1)*n) = 1, n=labelExp j^2.

Theorems p5_phase_relation and p5_phase_pow project the exact relation and the
mu2l phase condition.  This is a CONDITIONAL/named-data file: the relation is
NOT yet derived from the bridge (the map-zpow derivation remains GAP).  No
c_j=1 theorem is present.

### 8.14 label j=0 / nonzero-label separation

ThetaLabel = { j : SignedLabel l.value // 0 < j.1 }, i.e. positive
representatives 1..l*.  Hence j=0 is not an element of ThetaLabel and no
paperRootThetaUnit / qRoot^0 value is part of the label dictionary.  The
label-shift theorem oddThetaFraction_eval_thetaLabel is stated only for
ThetaLabel; thetaLabelExponent_pos records positivity.

If a downstream consumer needs the trivial j=0 value, it must be handled
separately as the constant 1 (or the corresponding normalized base point),
not as an additional ThetaLabel entry and not by adding zero to the product.
Any product over ThetaLabel therefore excludes 0 by construction; any
root-unit product that includes a j=0 factor needs an explicit separate
factor and a separate cancellation check.

Build status of P5 batch: GREEN.
- Mzk1P5QNormalizationInputActual: DONE EXIT=0 2026-11-12T22:37:38.457Z (70s).
- Mzk1P5PhaseRelationActual: DONE EXIT=0 2026-11-12T22:40:17.249Z (79s).
- Mzk1P5CJConditionActual: DONE EXIT=0 2026-11-12T22:46:19.423Z (75s).
All three have final axioms [propext, Classical.choice, Quot.sound] and no
sorryAx.  Mzk1P5LabelZeroSeparateActual is an optional Lean restatement of
section 8.14 and is not required for the P5 chain; its current per-file
open/argument issue does not affect the doc note.


### 8.15 root_image_zpow derived; phase relation residual

File: tmp/sheaf/xif/paper/Mzk1P5PhaseDerivedActual.lean (GREEN).

Theorem root_image_zpow:

  B.toRoot (B.r ^ N) = (B.qRoot : R) ^ ((l.value : Int) * N)

proved from B.root_image by map_zpow₀ plus zpow_natCast/zpow_mul.
Build: DONE EXIT=0 2026-11-12T23:01:07.767Z (70s); olean 34456 B; axioms
[propext, Classical.choice, Quot.sound].

The full phase relation is now also derived, not named:

  phase_relation (hunit : thetaUnit_j = qRoot^(j^2)) (j) :
    c_j * phase_j * qRoot^((l+1)*n) = 1.

Proof: root_image_zpow at N=-n gives qRoot^(-(l*n)) = toRoot(r^(-n));
B.comparison and hunit identify this with c_j*phase_j*qRoot^n; multiplying by
qRoot^(l*n) and using zpow_add₀ (qRoot is a unit, hence nonzero) yields 1.
The constants c_j/phase_j remain explicit parameters but the relation is no
longer a field.

Build: root_image_zpow and phase_relation both GREEN in the same file:
DONE EXIT=0 2026-11-12T23:04:16.665Z (61s); olean 143040 B; final axioms
[propext, Classical.choice, Quot.sound] for both, no sorryAx.
(The per-file log retains earlier failed attempts; the final DONE block is
decisive.)

LabelZeroSeparate file was deleted as optional; the j=0 note remains section
8.14.  extra-targets line should be removed by the lead.


### 8.16 derived c_j condition and root-choice order comparison

File 1: tmp/sheaf/xif/paper/Mzk1P5CJDerivedActual.lean.
Theorem c_eq_one_iff (hunit : thetaUnit_j=qRoot^(j^2)):

  B.c j = 1  <->  B.phase j * qRoot^((l+1)*n) = 1,   n=thetaLabelExponent j^2.

This is a theorem derived from phase_relation, not a structure field.

File 2: tmp/sheaf/xif/paper/Mzk1P5RootChoiceOrderActual.lean.
RootChoiceOrderData records qRoot^(2l)=q.  Then:
- root_pow_l_square: r=qRoot^l => r^2=q;
- root_pow_one_order: r=qRoot and r^2=q => qRoot^(2l)=qRoot^2.
Thus r |-> qRoot forces the nontrivial order condition
qRoot^(2(l-1))=1 (for qRoot nonzero), which fails for the actual
twoLthRootAt with nontrivial q.  The only square-compatible choice is
r |-> qRoot^l; this is exactly the corrected root_image used by A4/A8.

Build status: pending watchdog; no green claim until DONE EXIT=0.


### 8.17 P5 conditional chain: current green status and named inputs

Green: QNormalizationInput, PhaseRelation, CJCondition, PhaseDerived
(root_image_zpow + phase_relation), CJDerived (c_eq_one_iff theorem),
RootChoiceOrder (r |-> qRoot^l square-compatible; r |-> qRoot forces
qRoot^(2l)=qRoot^2 and the nontrivial order obstruction).

Named inputs remaining: analytic field map toRoot/r; root_image
toRoot r = qRoot^l; c_j; phase_j; comparison (CJ-L); actual analytic theta
value/Kummer identification.  No construction of the analytic/Kummer bridge
is asserted.

hunit is being derived in Mzk1P5HunitDerivedActual.lean from
paperRootThetaUnit = twoLthRootAt^(j^2) and actualP5Bridge_qRoot_eq via
zpow_natCast.  Status: pending watchdog; no green claim yet.

External search: Iut/EtaleTheta/KummerClass.lean contains project-specific
Kummer theory (HasKummerRoots, kummer classes), not a Mathlib port of the
analytic/root map.  No external Kummer formalization found that supplies the
analytic field map; the bridge remains a named input.


### 8.18 hunit derived; comparison is not an independent input

hunit is GREEN in tmp/sheaf/xif/paper/Mzk1P5HunitDerivedActual.lean:
DONE EXIT=0 2026-11-12T23:26:10.910Z (82s); olean 68232 B; final axioms
[propext, Classical.choice, Quot.sound].  In actualP5Bridge,
thetaUnit=paperRootThetaUnit and qRoot=twoLthRootAt; A5's identity plus
zpow_natCast and Units.val_pow_eq_pow_val gives
thetaUnit_j = qRoot^(thetaLabelExponent j ^2), with no hunit hypothesis.

Consequence for hcomparison: at the actual root image toRoot r = qRoot^l,
root_image_zpow gives toRoot(r^(-n)) = qRoot^(-(l*n)).  The comparison

  toRoot(r^(-n)) = c_j * phase_j * paperRootThetaUnit_j

is therefore equivalent, using paperRootThetaUnit_j = qRoot^n, to

  c_j * phase_j = qRoot^(-((l+1)*n)).

Thus hcomparison is NOT an independent field: for any phase_j it has the
canonical solution c_j := phase_j^(-1) * qRoot^(-((l+1)*n)).  This is exactly
the phase_relation already derived (with c chosen); the only remaining
content is the named choice of phase_j and the root image.  A Lean witness file is written:
tmp/sheaf/xif/paper/Mzk1P5ComparisonDerivedActual.lean.  It defines
paperRootThetaUnit_eq_qRoot_zpow, toRoot_zpow, cOfPhase, and proves
comparison_cOfPhase (hcomparison as a theorem).  Build status: pending
watchdog (not yet green); no green claim until DONE EXIT=0.

Why the analytic field map cannot be constructed from the current tree:
toRoot would have to be a ring homomorphism from the analytic oddTheta field L
(a normed field with its own place/q) to a single RootExtension G v0, while
the root side is place-indexed (RootExtension at each v) and the analytic
oddTheta input is not given as a number-field completion with a specified
place map.  No such global place-compatible homomorphism exists in the tree;
constructing one requires the actual analytic-to-algebraic place/Kummer
identification, which is exactly the missing source.  This is why toRoot/r
and root_image remain named inputs rather than a fabricated construction.


### 8.19 phase_j construction status and exact missing map

paperPhaseUnit m j = primitiveMu2lRoot.zeta ^ (m j) is an actual mu2l unit;
paperPhaseUnit_pow proves its 2l-th power is 1 (green in
Mzk1P5BridgeInstantiateActual).  Thus for any supplied m : ThetaLabel -> Nat,
phase_j is constructed and phase_pow holds.  What is NOT constructed is a
canonical map m : ThetaLabel -> Nat from the paper data; the phases in IUT II
Rem 2.5.1 are independent label-indexed mu2l elements, and no weight/phase
dictionary a_j (or m_j) is present in the formal objects.  Therefore phase_j
is actual up to the phase choice m, and the exact missing source is the
label-to-phase-exponent mapping, not a construction of a mu2l root.

ComparisonDerived file is GREEN: Mzk1P5ComparisonDerivedActual.lean,
DONE EXIT=0 2026-11-12T23:40:59.868Z (66s), olean 178464 B, axioms
[propext, Classical.choice, Quot.sound].  It constructs
paperRootThetaUnit_eq_qRoot_zpow, toRoot_zpow, cOfPhase and proves
comparison_cOfPhase, so hcomparison is now a theorem rather than a field.

PhaseExponentDataActual.lean adds the explicit label-to-exponent data:
structure PhaseExponentData (l) := (m : ThetaLabel -> Nat), and
phase_pow_actual proves paperPhaseUnit P.m j ^ (2l) = 1.  The phase unit is
actual for any supplied m; the only missing item is this m map itself (the
paper phase weights a_j/m_j), which cannot be inferred from the label alone.

Thus P5 named inputs now reduce to: root_image toRoot r=qRoot^l; analytic
field map toRoot/r; and the phase choice m.  c_j and hcomparison are
canonically defined by cOfPhase once comparison_cOfPhase is green.


### 8.20 P5 final conditional summary

File: tmp/sheaf/xif/paper/Mzk1P5FinalSummaryActual.lean.

structure P5NamedInputs (G v0 l) has exactly four fields:
  toRoot : L ->+* RootExtension G v0;
  r : L;
  root_image : toRoot r = twoLthRootAt^l;
  phase : PhaseExponentData l  (label->mu2l exponent m).

c_j and hcomparison are no longer inputs: cOfPhase is canonical and
comparison_cOfPhase is a theorem.  bridgeOfInputs constructs the bridge from
the four inputs, and p5_final_comparison gives

  I.toRoot(oddTheta q (i*r^j)/oddTheta q i)
    = cOfPhase_j * paperPhaseUnit_j * paperRootThetaUnit_j.

Build status: GREEN. Mzk1P5FinalSummaryActual DONE EXIT=0 2026-11-12T23:53:16.767Z
(53s); olean 298960 B; p5_final_comparison axioms
[propext, Classical.choice, Quot.sound].  PhaseExponentData DONE 23:47:58.
Acceptance summary: coord/P5-ACCEPTANCE.md.  Internal-consistency check
(L=R, toRoot=id, r=qRoot^l under hypothetical NormedField/Complete assumptions
on RootExtension) is in Mzk1P5InternalConsistencyActual.lean; it is not the
analytic bridge and does not claim an actual normed instance.

Remaining true GAP: the analytic field map toRoot/r and root_image still need
the actual place/Kummer identification; PhaseExponentData needs the paper
label-to-phase-exponent (a_j/m_j) dictionary.  None is fabricated.


### 8.21 P5 closeout: final input list and internal-consistency result

Final named inputs (P5NamedInputs):
1. toRoot : L ->+* RootExtension G v0 (analytic field map);
2. r : L (analytic root);
3. root_image : toRoot r = twoLthRootAt^l;
4. phase : PhaseExponentData l (label->mu2l exponent m).

c_j and hcomparison are constructed: cOfPhase/comparison_cOfPhase;
phase_relation and c_eq_one_iff are theorems; hunit is derived.

Final green file: Mzk1P5FinalSummaryActual.lean, DONE 2026-11-12T23:53:16.767Z,
olean 298960 B, p5_final_comparison axioms [propext, Classical.choice,
Quot.sound].

Internal consistency L=R, toRoot=id: attempted in
Mzk1P5InternalConsistencyActual.lean and FAILED.  Reasons:
(a) PhaseExponentData open omission (fixable);
(b) after adding hypothetical NormedField R, the induced Field instance differs
from the canonical AlgebraicClosure.instField, producing a typeclass diamond in
RingHom.id R; no fake normed/Field instance is allowed.
Thus the special case does not yield a lawful instance; the actual analytic
bridge remains the exact GAP.  Full acceptance record: coord/P5-ACCEPTANCE.md.

End of P5 closeout.
### 8.22 audit and internal-consistency final

Axiom audit file: tmp/sheaf/xif/paper/Mzk1P5AxiomAuditActual.lean.  It imports
the full P5 green chain and adds no theorem; #print axioms of all main
theorems.  DONE EXIT=0 2026-11-13T00:25:03.516Z (65s).  Output: every theorem
has only [propext, Classical.choice, Quot.sound], except root_pow_l_square /
root_pow_one_order which use [propext, Quot.sound]; no sorryAx.

InternalConsistency file is DONE EXIT=0 2026-11-13T00:13:57.050Z (56s) as a
conditional packaging theorem: given toRoot/r/root_image/phase, P5NamedInputs
is inhabited.  The stronger L=RootExtension, toRoot=id instance is NOT lawful:
hypothetical NormedField R introduces a Field instance differing from
AlgebraicClosure.instField, a typeclass diamond in RingHom.id; no fake normed
instance is added.  It is not the analytic bridge; actual analytic case GAP.

Final inputs remain the four in 8.21; STATE.md has the P5 row; acceptance is
coord/P5-ACCEPTANCE.md.

End of P5 branch.