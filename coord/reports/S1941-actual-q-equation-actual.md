# S1941: actual C3 / S1487Cand q versus the actual C6 canonical hull

Date: 2026-11-01. Task: for the actual paper-route C3 (q = S1487Cand) and the
actual C6 canonical hull/unit reference, compute both sides of the S1931
equation

    Real.log C3.thetaPacket.q
      = - (arithmeticTupleHullUnitLogVolume places tuple * card) / W,

prove it (hence SignedUnitFactorThetaComparison) or give the exact arithmetic
first missing. Do not fake.

Result: **missing**, with the exact arithmetic first missing isolated as

    S1941FirstMissing := arithmeticTupleHullUnitLogVolume actualPlaces actualTuple = 0.

The actual equation is **not** an equation about the completion q-parameter
S1487Cand.q: the actual theta packet of the paper-route C3 is the source-Haar
packet, whose parameter is one.

## 1. The actual data

The paper-route actual C3 is the S1391 L-carrier

    S1941ActualC3 l := S1487FaithfulC3 l
      ( = S1527C3 / S1920PaperC3 on the paper input ).

* s1941ActualC3_q : (S1941ActualC3 l).q = S1487Cand.
* s1941ActualC3_theta_q : (S1941ActualC3 l).thetaPacket.q = 1 (rfl; the
  S1487 theater family uses sourceHaarActualThetaPacket, q = 1, not
  sourceTheater, q = 1/5).
* The actual C6 data are the record's own
  S1941ActualPlaces l := (S1941ActualC3 l).tensorPlaces and
  S1941ActualTuple l := (S1941ActualC3 l).tensorTuple (concrete constant
  Gaussian five place at every tensor index, unique tuple point).

## 2. Both sides, exactly

* LHS: s1941ActualLHS_eq_zero : S1941ActualLHS l = 0.
* RHS: S1941ActualRHS l = -(S1941ActualHullVolume l * card) / W, and
  s1941ActualRHS_eq_zero_iff : S1941ActualRHS l = 0 iff S1941ActualHullVolume l = 0.
* s1941ActualQEquation_iff_firstMissing :
  S1941ActualQEquation l iff S1941FirstMissing l.
* s1941ActualRHS_nonpos: the actual RHS is at most zero, because the hull
  unit log-volume is nonnegative.

## 3. Exact first missing

    S1941FirstMissing l
      := arithmeticTupleHullUnitLogVolume (S1941ActualPlaces l)
           (S1941ActualTuple l) = 0.

Equivalent forms (proved):

* s1941FirstMissing_iff_hull_mass_eq: for any additive Haar measure mu,
  mu canonicalHull = mu canonicalUnitReference;
* s1941FirstMissing_iff_hullVolume_le_zero: H <= 0 (using H >= 0);
* if H > 0, the actual equation is false
  (s1941ActualQEquation_false_of_hullVolume_pos).

So the exact residual arithmetic content is: the actual C6 canonical hull and
the canonical unit reference have the same unit-relative Haar mass. It is not a
normalization question and not the S1487Cand completion norm.

## 4. Why the old-schema target is not instantiated here

SignedUnitFactorThetaComparison is typed on the old completion-valued
SourcePilotRegionData, which additionally requires a root system
NatRootSystem qUnit in the completion. The actual paper-route C3 is the
S1391 L-carrier: its roots live over the algebraic closure, and
SourcePilotRegion records that no completion root system is constructed.
Therefore the old target cannot be instantiated at the actual C3 without a fake
root-system inhabitant.

What is proved instead:

* s1941OldTarget_iff_hullVolume_eq_zero: for any old-schema C3 whose theta
  packet has q = 1, SignedUnitFactorThetaComparison at paperArithmeticHaar is
  equivalent to arithmeticTupleHullUnitLogVolume places tuple = 0. This is the
  exact old-schema bridge, conditional on an old C3 carrying the actual theta
  packet; the actual C3 supplies the packet but not the old record.
* s1941Actual_signedUnitFactorL_iff_firstMissing: the exact L-carrier form
  SignedUnitFactorThetaComparisonL (same signed packet average, same source
  Haar, same C6 canonical regions) at the actual C3 is equivalent to
  S1941FirstMissing.

Thus the whole residual content, in the carrier where the actual C3 lives, is
one named arithmetic proposition, S1941FirstMissing; it is not asserted.

## 5. Lean artifact

Target file:
  tmp/sheaf/xif/paper/S1941ActualQEquationActual.lean
  lines 359, bytes 18105,
  SHA256 887B9E57AE6C1A7AFE2833D9619248DFCB590081E998A50C238689843801445B.

Compile (from D:\lean):

    lake env lean -R D:/lean -s 65536 -M 8192
      -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1941ActualQEquationActual.olean
      tmp/sheaf/xif/paper/S1941ActualQEquationActual.lean

  EXIT=0, zero errors, zero warnings.
  Log: tmp/sheaf/xif/paper/_S1941_compile.log (1815 bytes).

Olean:
  .lake/build/lib/lean/tmp/sheaf/xif/paper/S1941ActualQEquationActual.olean
  bytes 272520,
  SHA256 85C0355C852D2564145E1FE01D9D6F4AD55088AD92EBCCC2BB19D245BDBA6559.

All 12 public declarations probed with #print axioms depend only on
[propext, Classical.choice, Quot.sound].

Consumer probe: tmp/sheaf/xif/paper/_S1941ConsumerProbe.lean EXIT=0,
imports the olean and checks the key signatures.

## 6. Boundary

* target_accepted = false: S1941FirstMissing is not proved; the actual
  equation is reduced to it exactly.
* No fake normalization, arbitrary data, axiom, sorry, True, or PUnit.
* Not run: full project build, comparator acceptance, independent human review.