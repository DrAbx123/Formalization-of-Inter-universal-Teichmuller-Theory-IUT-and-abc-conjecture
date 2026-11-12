# ROUTE3-PHASE — independent mu2l phases and the 2l-power readout ledger

Task: task-98, R29r-stepxi. Scope: C-Phase of route three; no new assumptions.
Snapshot: 2026-11-13T04:39:22+08:00 Asia/Shanghai (task time).
Paper anchor: IUT II Remark 2.5.1(iii),
papers/motizuki_corpus/text/Inter-universal Teichmuller Theory II.txt:4322-4343.
HANDOFF anchor: section 6.6, D:/iut-audit-20261113/COR312-THREE-ROUTES-HANDOFF-20261113.md:1002-1021.

## 0. Verdict

The independent phase condition is now an explicit, provable statement:
for a product with weights a_j, invariance under ALL independent mu2l phases
holds iff every a_j is divisible by 2l. The condition sum_j a_j = 0 is not
sufficient. Taking the 2l-th power removes all phase factors but multiplies
the logarithmic readout by 2l; this is a new object, not the original
comparison (IUT III (xi-h)).

Route-three consequence: for products/ratios over multiple labels one must
use an equivariant phase family, or use the 2l-power with an explicit 2l
readout factor. The existing paperRootThetaMuOrbit is a synchronized
single-phase orbit; it is insufficient for independent phases across labels.

## 1. Actual phase objects already in the tree

- PaperC3PrimitiveMu2lRootActual.lean: an actual primitive 2l-th root of
  unity in the algebraic closure; its structure records `zeta_pow` and
  `primitive_order` (roughly lines 21-50).
- PaperC3ThetaValuesActual.lean:
  - Mu2lRoot at line 50 (zeta with zeta^(2l)=1);
  - mu2lAction at line 55; mu2lAction_zero/add/period at lines 60-75;
  - paperQParameterMu2lOrbit at line 78 uses ONE R for all labels.
- PaperC3RootThetaHullActual.lean:
  - paperRootThetaMuPoint at line 46 uses `primitiveMu2lRoot` and the SAME
    exponent m for every label;
  - paperRootThetaMuOrbit at line 52; paperRootThetaHull at line 59.
- PaperC3ThetaRootActual.lean:61-72: paperRootThetaUnit is the root-valued
  q_v^(j^2); its mu2l orbit is the single-value orbit.

Thus the tree has a `mu2l`-action and a primitive root, but only a
synchronized diagonal action. It does not have a family of independent
phase choices indexed by labels.

## 2. Mathematical phase statement

Let M be a commutative monoid, I a finite label set, theta : I -> M,
and zeta : I -> M with zeta_i^(2l)=1. Define
  phaseAction zeta theta_i = zeta_i * theta_i.

### 2.1 Invariance criterion

The Lean file proves:

  (forall zeta, (forall i, zeta_i^(2l)=1) ->
      prod_i zeta_i^(a_i) = 1)
    iff (forall i, 2l divides a_i).

Proof of the forward direction: test one label i at a time, put a primitive
2l-root omega at i and 1 elsewhere; the product becomes omega^(a_i), so
primitivity forces 2l | a_i. The reverse direction is
(zeta_i^(2l))^(a_i/(2l)) = 1.

Note: this is for natural weights a_i. The integer-weight version is the
same statement with zpow; the counterexample below uses integer weights.

### 2.2 Sum-zero is NOT sufficient

Concrete counterexample for l >= 5 (so 2l >= 10): let omega be a primitive
2l-th root of unity, zeta_1 = omega, zeta_2 = omega^(-1), a_1 = 1,
a_2 = -1. Then
  a_1 + a_2 = 0,
  prod_i zeta_i^(a_i) = omega^1 * (omega^(-1))^(-1) = omega^2 != 1,
because omega has order 2l > 2. Hence the naive condition
`sum_j a_j = 0` does not make a product phase-independent.

### 2.3 Taking the 2l-th power

If zeta_i^(2l)=1 for all i, then
  (prod_i (zeta_i * theta_i)^(2l)) = prod_i theta_i^(2l).
This is the phase-killing identity. For a weighted product:
  (weightedProduct (phaseAction zeta theta) a)^(2l)
    = (weightedProduct theta a)^(2l).

Readout price: for x > 0,
  Real.log (x^(2l)) = 2l * Real.log x.
If the target readout is log-volume or a signed log, taking the 2l-th power
multiplies the absolute/logarithmic reading by 2l (and changes sign bookkeeping
according to the chosen convention). This must be recorded as an explicit
readout factor, not silently divided away.

## 3. Consequence for route three

1. A SINGLE theta value: the mu2l orbit is enough; choosing any representative
   changes the value by a mu2l factor and no product is involved.
2. A product or ratio over several independent labels: the synchronized
   `paperRootThetaMuOrbit` is not enough. Need either
   (a) an equivariant family: phases (zeta_j) indexed by labels, a principal
       homogeneous space/torsor, and an equivariant comparison morphism; or
   (b) the 2l-th power, with an explicit multiplication of the readout by 2l.
3. The 2l-power route is not the original comparison. IUT III (xi-h) explicitly
   distinguishes an N-th power of the original object from a newly generalized
   comparison process. The power route is an algebraic disambiguation, not a
   free proof of the original inequality.
4. A sum-zero shortcut (`sum a_j=0`) may suppress a diagonal phase but not
   independent phases; the counterexample in 2.2 is decisive.

## 4. Lean file and theorem list

File: tmp/sheaf/xif/paper/Mzk1PhaseEquivarianceActual.lean.
- phaseAction;
- weightedProduct;
- weightedProduct_phaseAction;
- independent_phase_invariant_iff;
- phase_product_pow_twoL;
- weightedProduct_pow_twoL;
- log_readout_pow_twoL.

Watchdog result:
- START 2026-11-12T20:47:25.049Z (final source)
- DONE EXIT=0 2026-11-12T20:47:54.126Z (29s)
- olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/Mzk1PhaseEquivarianceActual.olean
  (size 113424 B, mtime 2026-11-12T20:47:53Z)
- Final #print axioms:
  independent_phase_invariant_iff: [propext, Classical.choice, Quot.sound];
  phase_product_pow_twoL and weightedProduct_pow_twoL: [propext, Quot.sound];
  log_readout_pow_twoL: [propext, Classical.choice, Quot.sound].
  No sorryAx.
- The per-file log still contains earlier failed attempts; the final DONE block is
  decisive.

The explicit counterexample sum a_j=0 but product phase !=1 is given
mathematically in section 2.2; it is not additionally formalized as a Lean
theorem in this file. That is the one remaining formalization gap of this batch.

## 5. Exact gaps / next steps

- Missing: an actual label-indexed independent phase family on the paper root
  theta values, i.e. a map j -> mu2l-torsor/phase, not one global zeta^m.
- Missing: equivariance of the C-Theta comparison map under that family.
- Missing: a target readout convention for the 2l-power ledger (log-volume or
  signed log; absolute value; sign changes). The algebraic factor 2l is proved
  for positive real x; the target-specific sign/withTop ledger is open.
- The existing synchronized orbit remains valid for single values and for
  statements that are explicitly diagonal; it cannot justify independent
  product/ratio invariance.


## 6. task-103: label-indexed independent phase family and C-Theta equivariance

### 6.1 Actual phase family

File: tmp/sheaf/xif/paper/Mzk1PhaseTorsorActual.lean.

- ThetaPhaseFamily (G) := for every label j : ThetaLabel and place v,
  an independent unit of the root extension:
    (j : ThetaLabel) -> (v : V) -> (RootExtension (G := G) v)^x.
- phaseFamilyAction phase j is the pointwise product of phase j v with
  paperRootThetaUnit j v. It touches only label j and is independent across
  labels by construction; no diagonal embedding is assumed.
- synchronizedPhaseFamily m uses the SAME primitiveMu2lRoot^m at every label.
- synchronizedPhaseFamily_action proves this is exactly
  paperRootThetaMuPoint m (thetaLabelToSigned j).
- paperRootThetaMuOrbit_eq_range_synchronized proves the existing single
  orbit is the range of the synchronized family. Hence paperRootThetaMuOrbit
  is a proper special case, not the independent phase object.

### 6.2 Product/ratio condition

For a label-indexed phase family phase and weights a_j, the phase factor of a
weighted product is prod_j phase_j^(a_j). By task-98's
independent_phase_invariant_iff specialized at a place:

  invariance for every independent phase family
    iff every a_j is divisible by 2l.

The synchronized family is the special case phase_j = primitiveMu2lRoot^m for
all j; its product phase is (primitiveMu2lRoot^m)^(sum a_j), so a sum-zero
condition can cancel this diagonal factor while failing for independent phases.
The counterexample sum a_j=0 but product phase !=1 from section 2.2 applies.

### 6.3 C-Theta equivariance: exact status

The actual analytic odd theta series oddTheta has NO label or phase variable;
OddThetaShift/OddThetaNormalization prove only the phase-free shift law and
normalized special-value identity. The independent phase family above acts on
paperRootThetaUnit (root units in the algebraic closure), not on oddTheta.

Consequently:
- No actual theorem identifies oddTheta q (r^a U) with paperRootThetaUnit at a
  label; the C-Theta multiplicative-shift ratio cannot be promoted to an
  equivariant theorem on the existing analytic object.
- If one formally attaches phase multipliers za, zb, z0 to the three analytic
  factors, the ratio gains
      (za * zb) / z0^2.
  There is no source theorem forcing za*zb = z0^2; independent phases do not
  cancel. This is only a formal ledger, not an actual phase action on oddTheta.
- Exact missing bridge: an actual identification (or line-bundle section)
  between the analytic oddTheta values and the root-valued paper theta family,
  plus a label indexing of the C7 shifts; then equivariance can be stated.
  Until that bridge exists, the C-Theta equivariant theorem is BLOCKED; only
  the phase bookkeeping (sections 2-3) and the root-unit phase family are green.

### 6.4 Verdict

- Label-indexed independent phase family: constructed (ThetaPhaseFamily) with
  the synchronized orbit as a proved special case.
- C-Phase algebra: green (task-98); the independent-family object is now
  explicit.
- C-Theta equivariance: BLOCKED on the analytic/root-theta identification;
  not claimed. The formal phase factor za*zb/z0^2 is recorded so a future
  bridge has the correct ledger.


### 6.5 Build evidence for task-103

File: tmp/sheaf/xif/paper/Mzk1PhaseTorsorActual.lean.
- START 2026-11-12T20:56:28.749Z (final source)
- DONE EXIT=0 2026-11-12T20:57:30.370Z (62s)
- olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/Mzk1PhaseTorsorActual.olean
  (size 58536 B, mtime 2026-11-12T20:57:29Z)
- #print axioms:
  phaseFamilyAction, synchronizedPhaseFamily_action,
  paperRootThetaMuOrbit_eq_range_synchronized all depend only on
  [propext, Classical.choice, Quot.sound]; no sorryAx.
- The per-file log retains earlier failed attempts; the final DONE block is
  decisive.

### 6.6 Final C-Theta equivariance judgment

- The label-indexed independent phase family is green and the synchronized
  paperRootThetaMuOrbit is proved to be its range special case.
- The analytic oddTheta ratio remains phase-free; there is no actual bridge
  from oddTheta values to paperRootThetaUnit/labels. Therefore a genuine
  C-Theta equivariance theorem is NOT claimed; the exact missing bridge is
  the analytic/root-theta identification plus label indexing of the C7 shifts.
- The formal phase factor for a product/ratio is recorded: independent phases
  multiply the ratio by (za*zb)/z0^2; no source relation forces it to one.
- Route-three C-Phase object gap (label-indexed family) is now closed; the
  remaining C-Theta gap is the analytic-to-root/localization bridge.

End of report.