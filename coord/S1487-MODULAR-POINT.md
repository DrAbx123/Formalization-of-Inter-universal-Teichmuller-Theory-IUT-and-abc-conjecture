# S1487-MODULAR-POINT — Gaussian curve, 5-torsion, and modular-curve relation

Status: read-only; no compile.

## 1. What S1487 actually provides

- S1487Arithmetic l := concreteGaussianInitialThetaArithmeticData l
  (S1487OQPilotScalarEqualityActual:395).
- Its fields: Fmod = F = K = GaussianField (ConcreteFinitePlaceBoundary:25-31),
  and curve := concreteSplitPuncturedCurve.baseChange GaussianField.
  So there IS a punctured elliptic curve over GaussianField, but no level
  structure and no modular curve.
- S1487FivePlace : FinitePlaceAtPrime GaussianField 5
  (S1487...:128), value concreteGaussianFivePlace, a place above 5.
  It is a local place, not a modular curve point.
- S1487Cand : FinitePlaceQCandidate S1487FivePlace.val
  (S1487...:133), a q-candidate/uniformizer at that place. It has an order
  and local log magnitude; it is not a q-expansion or a modular form.
- S1487SourceData/FaithfulSourceData are SourceDefinition31Data records with
  badPlaces and qParameter; no level-5 structure, no X(5)/X_1(5) map.
- The curve's 5-torsion/Tate data are not constructed in S1487; the file only
  evaluates the C3/q side.

## 2. q-pilot ideal vs q-expansion/modular forms

S2735 qPilotIdeal is the product of Gaussian prime ideals above 5 and 2161;
S2736 log volume is log(absNorm). There is no definition in S2735/S2736 or
OrigXiFPaper series that maps a modular q-expansion or a modular form to this
ideal. The q in the analytic theta files is a real parameter q = 1/5
(Example36SourceThetaGenerator), not the same object as the ideal.

No existing theorem interprets qPilotLineBundle as a point of X(5)/X_1(5), nor
pulls a Klein/Siegel section back to O_K.

## 3. If one interprets q-pilot as a modular point: Lean draft

A minimal arithmetic model would be a structure (all fields explicit):

structure S1487ModularPointData (l : PrimeGeFive) where
  X : SchemeOver (Spec (NumberField.RingOfIntegers GaussianField))
  point : X
  level5 : LevelFiveStructure point
  thetaBundle : LineBundleOn X
  thetaSection : H0(thetaBundle)
  pullback_eq : pullback point thetaBundle = qPilotLineBundleC l
  section_eq : pullback point thetaSection = qPilotSection

Then the desirable conclusion is:

theorem S1487ModularPoint_qPilot_section_integral
    (D : S1487ModularPointData l) :
    IsIntegral (NumberField.RingOfIntegers GaussianField)
      (qPilotSection D) := ...

The integrality/rationality would follow if the point and section are defined
over O_K (or if the section is algebraic and the point is an O_K-point).
But this is conditional on the structure fields: no such X, point, level
structure, theta bundle, or pullback identification exists in the tree.

## 4. What is missing

1. Modular curve X(5) or X_1(5) with level structure over O_K/Q.
2. A point/component corresponding to the Gaussian curve/5-torsion data.
3. The theta/Klein line bundle and section on that modular curve.
4. A pullback comparison with qPilotLineBundle (divisor class equality).
5. Compatibility of the modular q-expansion with the Gaussian q-candidate.

## 5. Verdict

S1487 has a Gaussian elliptic curve and a local five-place/q-candidate, but no
level structure or modular curve. The q-pilot ideal is an O_K fractional ideal,
not a modular q-expansion. A modular-point interpretation is a new arithmetic
model (X(5)/X_1(5) + point + theta bundle + pullback), not a formalization
shortcut; the Lean draft above is a structure with explicit GAP fields, not a
proof.
