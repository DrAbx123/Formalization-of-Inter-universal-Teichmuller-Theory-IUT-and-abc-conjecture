import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlThetaObjectActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlThetaDivisorDegreeActual
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

/-!
# Line-bundle and theta-divisor boundary from the source arithmetic curve

This file attempts to derive the source theta line bundle and theta divisor from
the actual Definition 3.1 arithmetic curve and its Weierstrass model.

What is actually available and proved here:

* the actual punctured elliptic curve S.arithmetic.curve, its Weierstrass model,
  j-invariant, puncture, base change to K, sqrt(-1), and degree prime to l;
* the actual source theta-divisor type SourceThetaDivisor S, its weighted
  degree, Galois-invariance predicate, and the actual zero divisor;
* the actual integer degree and the real finite + archimedean principal degree
  from the product formula.

What is NOT derivable from the current source fields:

Definition 3.1 provides a number-field tower and a punctured elliptic curve
S.arithmetic.curve, but it has no field carrying a line bundle on that curve, no
theta object A_Theta, no chosen geometric theta divisor with a theta structure,
no unit comparison Mq -> M_Theta, and no mu_(2l)/l-Z/deck action or conjugate
synchronization.  These are enumerated exactly in
SourceThetaLineBundleMissingDatum below.

No formal independence theorem is claimed: Lean cannot prove that an arbitrary
choice construction will never inhabit a type.  The precise proved boundary is
that the six items are not fields of SourceDefinition31Data, are not projections
of the actual arithmetic curve record, and no construction of them is performed
in this file.  The exact additional source datum is listed.

No fake line bundle, theta object, unit comparison or deck action is introduced.
No theta spec, rank, or cardinal claim is used.
-/

namespace ABCBridge.SourceQlThetaLineBundleFromCurve

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.ThetaFieldTower
open LeanFormal.IUT.InfinitePlacePsiCnsResidual
open ABCBridge.SourceQlThetaObjectActual
open ABCBridge.SourceQlThetaDivisorDegreeActual
open scoped BigOperators

universe u

variable {l : LeanFormal.IUT.PrimeGeFive}
variable (S : SourceDefinition31Data.{u} l)

/-- Actual source arithmetic curve used by the line-bundle attempt. -/
abbrev sourceThetaLineBundleCurve : PuncturedEllipticCurve S.arithmetic.F :=
  S.arithmetic.curve

/-- Actual Weierstrass model of the source curve. -/
abbrev sourceThetaLineBundleWeierstrass :
    WeierstrassCurve S.arithmetic.F :=
  S.arithmetic.curve.curve

/-- Actual source curve base change to K. -/
abbrev sourceThetaLineBundleCurveK :
    PuncturedEllipticCurve S.arithmetic.K :=
  S.arithmetic.curve.baseChange S.arithmetic.K

/-- Actual theta-divisor type attached to the source curve data. -/
abbrev sourceThetaLineBundleDivisorType (S : SourceDefinition31Data.{u} l) : Type u := SourceThetaDivisor S

/-- Actual weighted degree on the source divisor type. -/
abbrev sourceThetaLineBundleDegree (S : SourceDefinition31Data.{u} l) :
    sourceThetaLineBundleDivisorType S → ℤ :=
  sourceThetaDegree S

/-- Actual Galois-invariance predicate. -/
abbrev sourceThetaLineBundleGalois (S : SourceDefinition31Data.{u} l) :
    sourceThetaLineBundleDivisorType S → Prop :=
  sourceGaloisInvariant S

/-- The actual curve is elliptic. -/
theorem sourceThetaLineBundleCurve_isElliptic :
    S.arithmetic.curve.curve.IsElliptic :=
  S.arithmetic.curve.isElliptic

/-- The actual curve has a Weierstrass j-invariant. -/
theorem sourceThetaLineBundleCurve_jInvariant :
    S.arithmetic.curve.jInvariant = S.arithmetic.curve.curve.j :=
  S.arithmetic.curve.jInvariant_spec

/-- The actual curve base change has the expected Weierstrass model. -/
theorem sourceThetaLineBundleCurve_baseChange :
    (S.arithmetic.curve.baseChange S.arithmetic.K).curve =
      S.arithmetic.curve.curve.baseChange S.arithmetic.K := rfl

/-- The actual source tower has sqrt(-1) in F. -/
theorem sourceThetaLineBundleCurve_hasSqrtNegOne :
    HasSqrtNegOne S.arithmetic.F :=
  sqrtNegOne_spec S.arithmetic.tower

/-- The actual tower degree F/Fmod is prime to l.value. -/
theorem sourceThetaLineBundleCurve_degreePrimeToL :
    Nat.Coprime (Module.finrank S.arithmetic.Fmod S.arithmetic.F) l.value :=
  degreePrimeToL_spec S.arithmetic.tower

/-- The actual divisor type is the integer-coefficient function type on the
infinite places; this is the only divisor object supplied by the source data. -/
theorem sourceThetaLineBundleDivisorType_eq :
    sourceThetaLineBundleDivisorType S =
      (NumberField.InfinitePlace S.arithmetic.F → ℤ) := rfl

/-- Actual weighted-degree formula. -/
theorem sourceThetaLineBundleDegree_formula
    (D : sourceThetaLineBundleDivisorType S) :
    sourceThetaLineBundleDegree S D =
      ∑ w : NumberField.InfinitePlace S.arithmetic.F,
        (NumberField.InfinitePlace.mult w : ℤ) * D w :=
  rfl

/-- Actual zero divisor of the source divisor type. -/
def sourceThetaLineBundleZeroDivisor :
    sourceThetaLineBundleDivisorType S :=
  sourceThetaObjectZeroDivisor S

/-- Actual zero-divisor degree. -/
theorem sourceThetaLineBundleZeroDivisor_degree :
    sourceThetaLineBundleDegree S
      (sourceThetaLineBundleZeroDivisor S) = 0 :=
  sourceThetaObjectZeroDivisor_degree S

/-- Actual zero-divisor Galois invariance. -/
theorem sourceThetaLineBundleZeroDivisor_galois :
    sourceThetaLineBundleGalois S
      (sourceThetaLineBundleZeroDivisor S) :=
  sourceThetaObjectZeroDivisor_galois S

/-- The actual divisor data available from the source curve: only the integer
divisor type, its weighted degree, and the zero divisor are constructed. -/
theorem sourceThetaLineBundleDivisor_available :
    sourceThetaLineBundleDivisorType S =
        (NumberField.InfinitePlace S.arithmetic.F → ℤ)
      ∧ sourceThetaLineBundleDegree S
        (sourceThetaLineBundleZeroDivisor S) = 0
      ∧ sourceThetaLineBundleGalois S
        (sourceThetaLineBundleZeroDivisor S) :=
  ⟨rfl, sourceThetaLineBundleZeroDivisor_degree S,
    sourceThetaLineBundleZeroDivisor_galois S⟩

/-- Exact missing line-bundle/theta data names.  No line-bundle carrier is
introduced: these are the additional source data that the Definition 3.1
contract does not contain. -/
inductive SourceThetaLineBundleMissingDatum
  | curveLineBundle
  | thetaObjectATheta
  | geometricThetaDivisor
  | unitComparisonMqMTheta
  | muTwoLDeckRootAction
  | conjugateSynchronization
  deriving DecidableEq, Repr

/-- The exact six additional source-data items required beyond the current
curve/divisor fields.  This list is bookkeeping only; it is not an object and
has no geometric witness. -/
def sourceThetaLineBundleMissingData (S : SourceDefinition31Data.{u} l) :
    List SourceThetaLineBundleMissingDatum :=
  [ .curveLineBundle,
    .thetaObjectATheta,
    .geometricThetaDivisor,
    .unitComparisonMqMTheta,
    .muTwoLDeckRootAction,
    .conjugateSynchronization ]

/-- Exactly six additional items are missing. -/
theorem sourceThetaLineBundleMissingData_length (S : SourceDefinition31Data.{u} l) :
    (sourceThetaLineBundleMissingData S).length = 6 := rfl

/-- The actual source fields supply the arithmetic curve and the integer divisor
type, but the missing line-bundle/theta list has six items. -/
theorem sourceThetaLineBundle_boundary :
    sourceThetaLineBundleCurve S = S.arithmetic.curve
      ∧ sourceThetaLineBundleDivisorType S =
        (NumberField.InfinitePlace S.arithmetic.F → ℤ)
      ∧ (sourceThetaLineBundleMissingData S).length = 6 :=
  ⟨rfl, rfl, sourceThetaLineBundleMissingData_length S⟩

/-- Exact additional source datum, listed by name.  The first item is a line
bundle on the actual arithmetic curve; the remaining five are the theta object,
geometric divisor, unit comparison, deck/root action and conjugate
synchronization. -/
theorem sourceThetaLineBundle_additionalDatum :
    (sourceThetaLineBundleMissingData S) =
      [ .curveLineBundle,
        .thetaObjectATheta,
        .geometricThetaDivisor,
        .unitComparisonMqMTheta,
        .muTwoLDeckRootAction,
        .conjugateSynchronization ] := rfl

/-- The curve data alone yields no line-bundle object in this construction;
the file proves only the actual curve/divisor facts and records the missing
datum.  This is a boundary statement, not an independence theorem. -/
theorem sourceThetaLineBundle_curveOnlyBoundary :
    sourceThetaLineBundleCurve S = S.arithmetic.curve
      ∧ sourceThetaLineBundleDegree S
        (sourceThetaLineBundleZeroDivisor S) = 0
      ∧ (sourceThetaLineBundleMissingData S).length = 6 :=
  ⟨rfl, sourceThetaLineBundleZeroDivisor_degree S,
    sourceThetaLineBundleMissingData_length S⟩

/-- Exact residual: actual curve/divisor data and the six missing items. -/
theorem sourceThetaLineBundle_exactResidual :
    sourceThetaLineBundleCurve S = S.arithmetic.curve
      ∧ sourceThetaLineBundleDivisorType S =
        (NumberField.InfinitePlace S.arithmetic.F → ℤ)
      ∧ sourceThetaLineBundleDegree S
        (sourceThetaLineBundleZeroDivisor S) = 0
      ∧ sourceThetaLineBundleGalois S
        (sourceThetaLineBundleZeroDivisor S)
      ∧ (sourceThetaLineBundleMissingData S).length = 6 :=
  ⟨rfl, rfl, sourceThetaLineBundleZeroDivisor_degree S,
    sourceThetaLineBundleZeroDivisor_galois S,
    sourceThetaLineBundleMissingData_length S⟩

/-- The actual real principal-divisor degree is zero for every global unit; this
uses the actual finite + archimedean product formula, not a line-bundle choice. -/
theorem sourceThetaLineBundlePrincipalDegree_zero
    (f : S.arithmetic.Fˣ) :
    sourcePrincipalFiniteDegree S f +
      sourcePrincipalArchimedeanDegree S f = 0 :=
  sourcePrincipalTotalDegree_zero S f

/-- The actual integer theta-divisor degree of the zero divisor is zero. -/
theorem sourceThetaLineBundleZeroDivisor_degree' :
    sourceThetaLineBundleDegree S
      (sourceThetaLineBundleZeroDivisor S) = 0 :=
  sourceThetaLineBundleZeroDivisor_degree S

/-- The actual zero divisor is Galois invariant. -/
theorem sourceThetaLineBundleZeroDivisor_galois' :
    sourceThetaLineBundleGalois S
      (sourceThetaLineBundleZeroDivisor S) :=
  sourceThetaLineBundleZeroDivisor_galois S

/-- The actual weighted degree is additive on the source divisor type. -/
theorem sourceThetaLineBundleDegree_add
    (D E : sourceThetaLineBundleDivisorType S) :
    sourceThetaLineBundleDegree S (D + E) =
      sourceThetaLineBundleDegree S D +
        sourceThetaLineBundleDegree S E :=
  sourceQlThetaDivisorDegreeActual_add S D E

/-- The actual weighted degree is negated on negation. -/
theorem sourceThetaLineBundleDegree_neg
    (D : sourceThetaLineBundleDivisorType S) :
    sourceThetaLineBundleDegree S (-D) =
      -sourceThetaLineBundleDegree S D :=
  sourceQlThetaDivisorDegreeActual_neg S D

/-- The actual zero divisor is the additive zero. -/
theorem sourceThetaLineBundleZeroDivisor_eq_zero :
    sourceThetaLineBundleZeroDivisor S =
      (0 : sourceThetaLineBundleDivisorType S) := rfl

/-- The actual curve data includes a Weierstrass model and j-invariant; no
line-bundle carrier is extracted from them. -/
theorem sourceThetaLineBundleCurve_weierstrass :
    sourceThetaLineBundleWeierstrass S = S.arithmetic.curve.curve
      ∧ S.arithmetic.curve.jInvariant = S.arithmetic.curve.curve.j :=
  ⟨rfl, sourceThetaLineBundleCurve_jInvariant S⟩

/-- The actual source curve base change is constructed. -/
theorem sourceThetaLineBundleCurveK_eq :
    sourceThetaLineBundleCurveK S =
      S.arithmetic.curve.baseChange S.arithmetic.K := rfl

/-- The exact additional datum list is the six named items; no line-bundle
carrier is defined. -/
theorem sourceThetaLineBundle_noCarrier :
    (sourceThetaLineBundleMissingData S).length = 6
      ∧ sourceThetaLineBundleDivisorType S =
        (NumberField.InfinitePlace S.arithmetic.F → ℤ) :=
  ⟨sourceThetaLineBundleMissingData_length S, rfl⟩

/-- The actual curve and divisor data, plus the exact missing line-bundle/theta
list, form the complete boundary of this file. -/
theorem sourceThetaLineBundle_finalBoundary :
    sourceThetaLineBundleCurve S = S.arithmetic.curve
      ∧ sourceThetaLineBundleDivisorType S =
        (NumberField.InfinitePlace S.arithmetic.F → ℤ)
      ∧ sourceThetaLineBundleDegree S
        (sourceThetaLineBundleZeroDivisor S) = 0
      ∧ (∀ f : S.arithmetic.Fˣ,
        sourcePrincipalFiniteDegree S f +
          sourcePrincipalArchimedeanDegree S f = 0)
      ∧ (sourceThetaLineBundleMissingData S).length = 6 :=
  ⟨rfl, rfl, sourceThetaLineBundleZeroDivisor_degree S,
    sourcePrincipalTotalDegree_zero S,
    sourceThetaLineBundleMissingData_length S⟩


end

end ABCBridge.SourceQlThetaLineBundleFromCurve
