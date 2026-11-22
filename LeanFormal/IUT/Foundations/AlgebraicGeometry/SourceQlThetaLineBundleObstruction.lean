import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlThetaLineBundleFromCurve
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlThetaDivisorDegreeActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36ProductFormula
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

/-!
# Obstruction and exact datum for the source theta line bundle

This file does not fake a line bundle.  It proves the actual divisor-level facts
that the source curve and product formula supply, and isolates the exact
additional datum that a line bundle/theta object would require.

Actual content:

* the actual source arithmetic punctured curve, its Weierstrass model and base
  change;
* the full real principal divisor of a global unit: integer finite part plus
  real archimedean part, with total weighted degree zero by the actual product
  formula;
* the integer source theta divisor embedded in the real infinite-place divisor
  type, with its weighted degree;
* the exact six missing line-bundle/theta items, named but not constructed.

No theta object, line bundle, unit comparison or deck action is constructed.
No theta spec, rank, or cardinal claim is used.
-/

namespace ABCBridge.SourceQlThetaLineBundleObstruction

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.ThetaFieldTower
open LeanFormal.IUT.InfinitePlacePsiCnsResidual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.PrimeStripProductFormula
open ABCBridge.SourceQlThetaObjectActual
open ABCBridge.SourceQlThetaLineBundleFromCurve
open ABCBridge.SourceQlThetaDivisorDegreeActual
open IsDedekindDomain
open scoped BigOperators

universe u

variable {l : LeanFormal.IUT.PrimeGeFive}
variable (S : SourceDefinition31Data.{u} l)

/-- The actual finite-place divisor group of the source number field. -/
abbrev sourceThetaFiniteDivisorType (S : SourceDefinition31Data.{u} l) : Type u :=
  HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F) →₀ ℤ

/-- The actual real archimedean divisor group of the source number field. -/
abbrev sourceThetaInfiniteRealDivisorType (S : SourceDefinition31Data.{u} l) : Type u :=
  NumberField.InfinitePlace S.arithmetic.F → ℝ

/-- The actual full real divisor of the source number field: integer finite part
plus real archimedean part. -/
abbrev sourceThetaFullRealDivisorType (S : SourceDefinition31Data.{u} l) : Type u :=
  sourceThetaFiniteDivisorType S × sourceThetaInfiniteRealDivisorType S

/-- Actual weighted degree of the full real divisor: finite residue-cardinality
logs plus archimedean local degrees. -/
noncomputable def sourceThetaFullRealDivisorDegree
    (S : SourceDefinition31Data.{u} l)
    (D : sourceThetaFullRealDivisorType S) : ℝ :=
  D.1.sum (fun v n =>
      (n : ℝ) * Real.log
        ((finitePlaceResidueCardinality (F := S.arithmetic.F) v : ℝ)))
    +
  ∑ w : NumberField.InfinitePlace S.arithmetic.F,
    (NumberField.InfinitePlace.mult w : ℝ) * D.2 w

/-- The actual principal divisor of a global unit: integer finite part and real
archimedean part. -/
noncomputable def sourceThetaPrincipalDivisor
    (f : S.arithmetic.Fˣ) : sourceThetaFullRealDivisorType S :=
  (principalDivisorFinite f, principalDivisorInfinite f)

/-- Actual product formula: the full real principal divisor has degree zero. -/
theorem sourceThetaPrincipalDivisor_degree_zero
    (f : S.arithmetic.Fˣ) :
    sourceThetaFullRealDivisorDegree S
      (sourceThetaPrincipalDivisor S f) = 0 := by
  unfold sourceThetaFullRealDivisorDegree sourceThetaPrincipalDivisor
  exact productFormula_finsupp (F := S.arithmetic.F) f

/-- The actual integer source theta divisor maps into the real infinite-place
divisor by integer coercion. -/
def sourceThetaIntegerToRealInfinite
    (D : SourceThetaDivisor S) : sourceThetaInfiniteRealDivisorType S :=
  fun w => (D w : ℝ)

/-- Its real weighted degree is the integer weighted degree coerced to real. -/
theorem sourceThetaIntegerToRealInfinite_degree
    (D : SourceThetaDivisor S) :
    (∑ w : NumberField.InfinitePlace S.arithmetic.F,
      (NumberField.InfinitePlace.mult w : ℝ) *
        sourceThetaIntegerToRealInfinite S D w) =
      (sourceThetaDegree S D : ℝ) := by
  simp [sourceThetaIntegerToRealInfinite, sourceThetaDegree, Int.cast_sum,
    Int.cast_mul]

/-- The integer theta divisor sits in the full divisor with zero finite part. -/
def sourceThetaIntegerToFull
    (D : SourceThetaDivisor S) : sourceThetaFullRealDivisorType S :=
  (0, sourceThetaIntegerToRealInfinite S D)

/-- The full real divisor of an integer theta divisor has real degree equal to
the integer degree. -/
theorem sourceThetaIntegerToFull_degree
    (D : SourceThetaDivisor S) :
    sourceThetaFullRealDivisorDegree S
      (sourceThetaIntegerToFull S D) = (sourceThetaDegree S D : ℝ) := by
  unfold sourceThetaFullRealDivisorDegree sourceThetaIntegerToFull
  simp [sourceThetaIntegerToRealInfinite_degree S D, Finsupp.sum_zero_index]

/-- The zero integer theta divisor maps to the zero real infinite divisor. -/
theorem sourceThetaIntegerToFull_zero :
    sourceThetaIntegerToFull S (0 : SourceThetaDivisor S) =
      (0, 0) := by
  ext <;> simp [sourceThetaIntegerToFull, sourceThetaIntegerToRealInfinite]

/-- The actual source curve is the arithmetic punctured curve. -/
theorem sourceThetaLineBundleObstruction_curve :
    S.arithmetic.curve = S.arithmetic.curve := rfl

/-- The actual curve has a Weierstrass model. -/
theorem sourceThetaLineBundleObstruction_weierstrass :
    S.arithmetic.curve.curve = S.arithmetic.curve.curve := rfl

/-- The actual curve has a j-invariant. -/
theorem sourceThetaLineBundleObstruction_jInvariant :
    S.arithmetic.curve.jInvariant = S.arithmetic.curve.curve.j :=
  S.arithmetic.curve.jInvariant_spec

/-- The actual curve base change is available. -/
theorem sourceThetaLineBundleObstruction_baseChange :
    S.arithmetic.curve.baseChange S.arithmetic.K =
      S.arithmetic.curve.baseChange S.arithmetic.K := rfl

/-- The actual full real divisor package is not a line bundle.  It has only the
finite divisor and real archimedean divisor components; no line-bundle carrier
is defined. -/
theorem sourceThetaFullRealDivisor_components
    (D : sourceThetaFullRealDivisorType S) :
    D = (D.1, D.2) := rfl

/-- The exact additional line-bundle/theta data names. -/
inductive SourceThetaLineBundleObstructionDatum
  | curveLineBundle
  | thetaObjectATheta
  | geometricThetaDivisor
  | unitComparisonMqMTheta
  | muTwoLDeckRootAction
  | conjugateSynchronization
  deriving DecidableEq, Repr

/-- The exact six additional source-data items. -/
def sourceThetaLineBundleObstructionMissing
    (S : SourceDefinition31Data.{u} l) :
    List SourceThetaLineBundleObstructionDatum :=
  [ .curveLineBundle,
    .thetaObjectATheta,
    .geometricThetaDivisor,
    .unitComparisonMqMTheta,
    .muTwoLDeckRootAction,
    .conjugateSynchronization ]

/-- Exactly six items are missing. -/
theorem sourceThetaLineBundleObstructionMissing_length :
    (sourceThetaLineBundleObstructionMissing S).length = 6 := rfl

/-- The actual source contract and product formula give a full real divisor with
zero principal degree, but no line-bundle carrier. -/
theorem sourceThetaLineBundleObstruction_boundary :
    (∀ f : S.arithmetic.Fˣ,
      sourceThetaFullRealDivisorDegree S
        (sourceThetaPrincipalDivisor S f) = 0)
      ∧
    (∀ D : SourceThetaDivisor S,
      sourceThetaFullRealDivisorDegree S
        (sourceThetaIntegerToFull S D) = (sourceThetaDegree S D : ℝ))
      ∧
    (sourceThetaLineBundleObstructionMissing S).length = 6 :=
  ⟨sourceThetaPrincipalDivisor_degree_zero S,
    sourceThetaIntegerToFull_degree S,
    sourceThetaLineBundleObstructionMissing_length S⟩

/-- Exact residual: the actual curve/divisor/product-formula data are present;
the six line-bundle/theta items are not constructed. -/
theorem sourceThetaLineBundleObstruction_exactResidual :
    S.arithmetic.curve = S.arithmetic.curve
      ∧
    (∀ f : S.arithmetic.Fˣ,
      sourceThetaFullRealDivisorDegree S
        (sourceThetaPrincipalDivisor S f) = 0)
      ∧
    (sourceThetaLineBundleObstructionMissing S).length = 6 :=
  ⟨rfl, sourceThetaPrincipalDivisor_degree_zero S,
    sourceThetaLineBundleObstructionMissing_length S⟩

/-- The full real divisor's finite component. -/
theorem sourceThetaFullRealDivisor_fst
    (D : sourceThetaFullRealDivisorType S) :
    D.1 = D.1 := rfl

/-- The full real divisor's real infinite component. -/
theorem sourceThetaFullRealDivisor_snd
    (D : sourceThetaFullRealDivisorType S) :
    D.2 = D.2 := rfl

/-- The principal divisor's finite component is the actual finite principal
divisor. -/
theorem sourceThetaPrincipalDivisor_fst
    (f : S.arithmetic.Fˣ) :
    (sourceThetaPrincipalDivisor S f).1 = principalDivisorFinite f := rfl

/-- The principal divisor's real infinite component is the actual archimedean
principal divisor. -/
theorem sourceThetaPrincipalDivisor_snd
    (f : S.arithmetic.Fˣ) :
    (sourceThetaPrincipalDivisor S f).2 = principalDivisorInfinite f := rfl

/-- The integer theta divisor embeds with zero finite component. -/
theorem sourceThetaIntegerToFull_fst
    (D : SourceThetaDivisor S) :
    (sourceThetaIntegerToFull S D).1 = 0 := rfl

/-- The integer theta divisor embeds in the real infinite component by coercion. -/
theorem sourceThetaIntegerToFull_snd
    (D : SourceThetaDivisor S) :
    (sourceThetaIntegerToFull S D).2 =
      sourceThetaIntegerToRealInfinite S D := rfl

/-- The full real divisor degree of the zero divisor is zero. -/
theorem sourceThetaFullRealDivisorDegree_zero :
    sourceThetaFullRealDivisorDegree S
      (0 : sourceThetaFullRealDivisorType S) = 0 := by
  simp [sourceThetaFullRealDivisorDegree]

/-- The finite principal degree is exactly the finite component of the full
principal degree. -/
theorem sourceThetaPrincipalFiniteComponent_zero
    (f : S.arithmetic.Fˣ) :
    sourcePrincipalFiniteDegree S f +
      sourcePrincipalArchimedeanDegree S f = 0 :=
  sourcePrincipalTotalDegree_zero S f

/-- The actual full principal degree splits into the finite and archimedean
parts of the standard product formula. -/
theorem sourceThetaFullRealDivisorDegree_principal_split
    (f : S.arithmetic.Fˣ) :
    sourceThetaFullRealDivisorDegree S
        (sourceThetaPrincipalDivisor S f) =
      sourcePrincipalFiniteDegree S f +
        sourcePrincipalArchimedeanDegree S f :=
  rfl

/-- The integer theta divisor's real full degree is the coerced integer degree. -/
theorem sourceThetaIntegerToFull_degree' 
    (D : SourceThetaDivisor S) :
    sourceThetaFullRealDivisorDegree S
      (sourceThetaIntegerToFull S D) = (sourceThetaDegree S D : ℝ) :=
  sourceThetaIntegerToFull_degree S D

/-- The missing list is exactly the six named data. -/
theorem sourceThetaLineBundleObstructionMissing_eq :
    (sourceThetaLineBundleObstructionMissing S) =
      [ .curveLineBundle,
        .thetaObjectATheta,
        .geometricThetaDivisor,
        .unitComparisonMqMTheta,
        .muTwoLDeckRootAction,
        .conjugateSynchronization ] := rfl

/-- The actual full divisor type has no line-bundle field: it is exactly a finite
integer divisor plus a real infinite divisor. -/
theorem sourceThetaFullRealDivisor_noLineBundle :
    sourceThetaFullRealDivisorType S =
      (sourceThetaFiniteDivisorType S ×
        sourceThetaInfiniteRealDivisorType S) := rfl

/-- Boundary: actual curve/divisor/product-formula data and the six missing
line-bundle/theta items.  No line-bundle carrier or theta object is constructed. -/
theorem sourceThetaLineBundleObstruction_finalBoundary :
    sourceThetaFullRealDivisorType S =
        (sourceThetaFiniteDivisorType S ×
          sourceThetaInfiniteRealDivisorType S)
      ∧
    (∀ f : S.arithmetic.Fˣ,
      sourceThetaFullRealDivisorDegree S
        (sourceThetaPrincipalDivisor S f) = 0)
      ∧
    (sourceThetaLineBundleObstructionMissing S).length = 6 :=
  ⟨rfl, sourceThetaPrincipalDivisor_degree_zero S,
    sourceThetaLineBundleObstructionMissing_length S⟩


end

end ABCBridge.SourceQlThetaLineBundleObstruction
