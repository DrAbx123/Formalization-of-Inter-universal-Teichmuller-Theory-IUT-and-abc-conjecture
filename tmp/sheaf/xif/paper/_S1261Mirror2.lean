import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.Foundations.AlgebraicGeometry.InfinitePlacePsiCnsResidual
import LeanFormal.IUT.Foundations.Geometry.PuncturedEllipticCurve
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

/-!
# Actual source theta object data from the arithmetic curve

This file attempts the actual source theta object/divisor data that follows from
a Definition 3.1 source S and its arithmetic curve.  It constructs only:

* the actual base fields F, Fmod, K and the actual Galois tower;
* the actual punctured elliptic curve S.arithmetic.curve, its Weierstrass
  curve, puncture, j-invariant and base change to K;
* the actual source theta-divisor type SourceThetaDivisor S (integer
  coefficient functions on the infinite places of F), its weighted degree and
  Galois-invariance predicate;
* the actual source integral-unit group and product-formula normalization;
* the actual zero divisor, with proved degree zero and Galois invariance.

## Missing data, stated not invented

The Definition 3.1 source contract has no line-bundle field on the arithmetic
curve, no theta object A_Theta, no chosen geometric theta divisor with a theta
structure, no unit comparison Mq -> M_Theta, and no mu_(2l)/l-Z/deck action or
conjugate synchronization.  These are enumerated exactly in
SourceThetaObjectMissingDatum below.  No arbitrary carrier, fake theta object,
or fake line bundle is introduced.

No theta spec, rank, or cardinal claim is used.
-/

namespace ABCBridge.SourceQlThetaObjectActual

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InfinitePlacePsiCnsResidual
open scoped BigOperators

universe u

variable {l : LeanFormal.IUT.PrimeGeFive}
variable (S : SourceDefinition31Data.{u} l)

/-- Actual source base field F. -/
abbrev sourceThetaObjectBaseField (S : SourceDefinition31Data.{u} l) : Type u := S.arithmetic.F

/-- Actual source base subfield Fmod. -/
abbrev sourceThetaObjectBaseSubfield (S : SourceDefinition31Data.{u} l) : Type u := S.arithmetic.Fmod

/-- Actual source theta field K. -/
abbrev sourceThetaObjectThetaField (S : SourceDefinition31Data.{u} l) : Type u := S.arithmetic.K

/-- Actual arithmetic punctured elliptic curve. -/
abbrev sourceThetaObjectCurve : PuncturedEllipticCurve S.arithmetic.F :=
  S.arithmetic.curve

/-- Actual Weierstrass model of the source curve. -/
abbrev sourceThetaObjectWeierstrassCurve : WeierstrassCurve S.arithmetic.F :=
  S.arithmetic.curve.curve

/-- Actual puncture point. -/
abbrev sourceThetaObjectPuncture :
    S.arithmetic.curve.curve.toProjective.Point :=
  S.arithmetic.curve.puncture

/-- Actual curve base change to K. -/
abbrev sourceThetaObjectCurveBaseChangeK :
    PuncturedEllipticCurve S.arithmetic.K :=
  S.arithmetic.curve.baseChange S.arithmetic.K

/-- Actual source theta-divisor type. -/
abbrev sourceThetaObjectDivisorType (S : SourceDefinition31Data.{u} l) : Type u := SourceThetaDivisor S

/-- Actual weighted theta-degree formula. -/
abbrev sourceThetaObjectDivisorDegree : sourceThetaObjectDivisorType S → ℤ :=
  sourceThetaDegree S

/-- Actual Galois-invariance predicate. -/
abbrev sourceThetaObjectDivisorGaloisInvariant :
    sourceThetaObjectDivisorType S → Prop :=
  sourceGaloisInvariant S

/-- Actual source integral-unit group. -/
abbrev sourceThetaObjectIntegralUnits (S : SourceDefinition31Data.{u} l) : Type u := SourceIntegralUnits S

/-- Actual product-formula normalization predicate. -/
abbrev sourceThetaObjectGlobalNormalization :
    sourceThetaObjectIntegralUnits S → Prop :=
  sourceGlobalNormalization S

/-- Actual source curve projection theorem. -/
theorem sourceThetaObjectCurve_eq :
    sourceThetaObjectCurve S = S.arithmetic.curve := rfl

/-- The actual source curve is elliptic. -/
theorem sourceThetaObjectCurve_isElliptic :
    S.arithmetic.curve.curve.IsElliptic :=
  S.arithmetic.curve.isElliptic

/-- The actual j-invariant is the Weierstrass-curve j-invariant. -/
theorem sourceThetaObjectCurve_jInvariant :
    S.arithmetic.curve.jInvariant = S.arithmetic.curve.curve.j :=
  S.arithmetic.curve.jInvariant_spec

/-- Base change of the actual curve has the expected Weierstrass model. -/
theorem sourceThetaObjectCurve_baseChange_curve :
    (S.arithmetic.curve.baseChange S.arithmetic.K).curve =
      S.arithmetic.curve.curve.baseChange S.arithmetic.K := rfl

/-- The actual arithmetic tower has sqrt(-1) in F. -/
theorem sourceThetaObjectCurve_hasSqrtNegOne :
    HasSqrtNegOne S.arithmetic.F :=
  sqrtNegOne_spec S.arithmetic.tower

/-- The actual tower degree from Fmod to F is prime to l.value. -/
theorem sourceThetaObjectCurve_degreePrimeToL :
    Nat.Coprime (Module.finrank S.arithmetic.Fmod S.arithmetic.F) l.value :=
  degreePrimeToL_spec S.arithmetic.tower

/-- Actual source theta-divisor type has the expected carrier. -/
theorem sourceThetaObjectDivisorType_eq :
    sourceThetaObjectDivisorType S = (NumberField.InfinitePlace S.arithmetic.F → ℤ) :=
  rfl

/-- The weighted degree formula of an actual source divisor. -/
theorem sourceThetaObjectDivisorDegree_apply
    (D : sourceThetaObjectDivisorType S) :
    sourceThetaObjectDivisorDegree S D =
      ∑ w : NumberField.InfinitePlace S.arithmetic.F,
        (NumberField.InfinitePlace.mult w : ℤ) * D w :=
  rfl

/-- The zero source theta divisor.  This is the actual zero coefficient function
on the source divisor type, not a chosen geometric theta divisor. -/
def sourceThetaObjectZeroDivisor : sourceThetaObjectDivisorType S :=
  fun _ => 0

/-- The zero divisor has degree zero by the actual weighted formula. -/
theorem sourceThetaObjectZeroDivisor_degree :
    sourceThetaObjectDivisorDegree S (sourceThetaObjectZeroDivisor S) = 0 := by
  simp [sourceThetaObjectDivisorDegree, sourceThetaObjectZeroDivisor,
    sourceThetaDegree]

/-- The zero divisor is Galois invariant by the actual definition. -/
theorem sourceThetaObjectZeroDivisor_galois :
    sourceThetaObjectDivisorGaloisInvariant S
      (sourceThetaObjectZeroDivisor S) := by
  intro σ w
  rfl

/-- Actual source divisor data available from the contract: the zero divisor has
degree zero and is Galois invariant.  This does not construct a theta divisor. -/
theorem sourceThetaObjectDivisor_available :
    sourceThetaObjectDivisorDegree S (sourceThetaObjectZeroDivisor S) = 0
      ∧ sourceThetaObjectDivisorGaloisInvariant S
        (sourceThetaObjectZeroDivisor S) :=
  ⟨sourceThetaObjectZeroDivisor_degree S,
    sourceThetaObjectZeroDivisor_galois S⟩

/-- The actual integral-unit carrier is the unit group of the ring of integers
of F. -/
theorem sourceThetaObjectIntegralUnits_eq :
    sourceThetaObjectIntegralUnits S =
      (NumberField.RingOfIntegers S.arithmetic.F)ˣ :=
  rfl

/-- The actual source integral-unit logarithm at an infinite place. -/
def sourceThetaObjectIntegralUnitLog
    (w : NumberField.InfinitePlace S.arithmetic.F)
    (u : sourceThetaObjectIntegralUnits S) : ℝ :=
  sourceIntegralUnitLog S w u

/-- The actual product-formula normalization is the source predicate, with no
inhabitant claimed. -/
theorem sourceThetaObjectGlobalNormalization_iff
    (u : sourceThetaObjectIntegralUnits S) :
    sourceThetaObjectGlobalNormalization S u ↔
      ∑ w : NumberField.InfinitePlace S.arithmetic.F,
        (NumberField.InfinitePlace.mult w : ℝ) *
          sourceThetaObjectIntegralUnitLog S w u = 0 :=
  rfl

/-- Exact missing source theta data.  These are names of data not present in the
Definition 3.1 contract; no object or inhabitant is invented. -/
inductive SourceThetaObjectMissingDatum
  | arithmeticCurveLineBundle
  | thetaObjectATheta
  | geometricThetaDivisor
  | unitComparisonMqMTheta
  | muTwoLDeckRootAction
  | conjugateSynchronization
  deriving DecidableEq, Repr

/-- Exact missing-data list, documentation and bookkeeping only. -/
def sourceThetaObjectMissingData (S : SourceDefinition31Data.{u} l) : List SourceThetaObjectMissingDatum :=
  [ .arithmeticCurveLineBundle,
    .thetaObjectATheta,
    .geometricThetaDivisor,
    .unitComparisonMqMTheta,
    .muTwoLDeckRootAction,
    .conjugateSynchronization ]

/-- There are exactly six missing source-theta items. -/
theorem sourceThetaObjectMissingData_length (S : SourceDefinition31Data.{u} l) :
    (sourceThetaObjectMissingData S).length = 6 := rfl

/-- Actual available curve/divisor/unit data and the exact six missing items. -/
theorem sourceThetaObjectAvailable_exactResidual :
    sourceThetaObjectCurve S = S.arithmetic.curve
      ∧
    sourceThetaObjectDivisorType S =
      (NumberField.InfinitePlace S.arithmetic.F → ℤ)
      ∧
    sourceThetaObjectDivisorDegree S (sourceThetaObjectZeroDivisor S) = 0
      ∧
    (sourceThetaObjectMissingData S).length = 6 :=
  ⟨rfl, rfl,
    sourceThetaObjectZeroDivisor_degree S,
    sourceThetaObjectMissingData_length S⟩

/-- The actual source curve data does not by itself construct a line bundle or a
theta object; the missing enumeration records that boundary. -/
theorem sourceThetaObject_curveOnlyBoundary :
    sourceThetaObjectCurve S = S.arithmetic.curve
      ∧ (sourceThetaObjectMissingData S).length = 6 :=
  ⟨rfl, sourceThetaObjectMissingData_length S⟩

/-- The exact missing line-bundle/theta-object data is not replaced by a fake
carrier: only its names and the actual available curve/divisor data are present. -/
theorem sourceThetaObject_noFakeThetaObject :
    (sourceThetaObjectMissingData S).length = 6
      ∧ sourceThetaObjectDivisorDegree S (sourceThetaObjectZeroDivisor S) = 0 :=
  ⟨sourceThetaObjectMissingData_length S,
    sourceThetaObjectZeroDivisor_degree S⟩

/-- The weighted degree of the zero divisor is zero. -/
theorem sourceThetaObjectDivisorDegree_zero :
    sourceThetaObjectDivisorDegree S (fun _ => (0 : ℤ)) = 0 := by
  simp [sourceThetaObjectDivisorDegree, sourceThetaDegree]

/-- The weighted degree is additive on actual source divisors. -/
theorem sourceThetaObjectDivisorDegree_add
    (D E : sourceThetaObjectDivisorType S) :
    sourceThetaObjectDivisorDegree S (D + E) =
      sourceThetaObjectDivisorDegree S D +
        sourceThetaObjectDivisorDegree S E := by
  simp [sourceThetaObjectDivisorDegree, sourceThetaDegree,
    Finset.sum_add_distrib, mul_add]

/-- The weighted degree changes sign under negation. -/
theorem sourceThetaObjectDivisorDegree_neg
    (D : sourceThetaObjectDivisorType S) :
    sourceThetaObjectDivisorDegree S (fun w => -(D w)) =
      -sourceThetaObjectDivisorDegree S D := by
  simp [sourceThetaObjectDivisorDegree, sourceThetaDegree,
    Finset.sum_neg_distrib, mul_neg]

/-- The zero divisor is the additive zero of the actual source divisor type. -/
theorem sourceThetaObjectZeroDivisor_eq_zero :
    sourceThetaObjectZeroDivisor S =
      (fun _ : NumberField.InfinitePlace S.arithmetic.F => (0 : ℤ)) := rfl

/-- The zero divisor has the actual additive degree zero. -/
theorem sourceThetaObjectZeroDivisor_degree' :
    sourceThetaObjectDivisorDegree S (sourceThetaObjectZeroDivisor S) = 0 :=
  sourceThetaObjectDivisorDegree_zero S

/-- The actual base change preserves the Weierstrass model equation. -/
theorem sourceThetaObjectCurve_baseChange_model :
    (S.arithmetic.curve.baseChange S.arithmetic.K).curve =
      S.arithmetic.curve.curve.baseChange S.arithmetic.K := rfl

/-- The actual source curve has a Weierstrass equation carrier. -/
theorem sourceThetaObjectCurve_weierstrass :
    (sourceThetaObjectCurve S).curve = S.arithmetic.curve.curve := rfl

/-- The actual source theta-divisor type is a function type, with no additional
fabricated geometric structure. -/
theorem sourceThetaObjectDivisorType_function :
    sourceThetaObjectDivisorType S =
      (NumberField.InfinitePlace S.arithmetic.F → ℤ) := rfl

/-- The actual available theta object data is the curve/divisor/unit data only;
the missing line-bundle/theta-object data is recorded, not invented. -/
theorem sourceThetaObject_availableBoundary :
    sourceThetaObjectCurve S = S.arithmetic.curve
      ∧ sourceThetaObjectIntegralUnits S =
        (NumberField.RingOfIntegers S.arithmetic.F)ˣ
      ∧ (sourceThetaObjectMissingData S).length = 6 :=
  And.intro rfl (And.intro rfl (sourceThetaObjectMissingData_length S))


end

end ABCBridge.SourceQlThetaObjectActual
