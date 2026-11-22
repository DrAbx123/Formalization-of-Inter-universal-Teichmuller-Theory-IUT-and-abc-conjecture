import tmp.sheaf.xif.paper.ThetaTensorScaledImageActual
import tmp.sheaf.xif.paper.QVFamThetaImageActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure

/-! # Actual qVFamily tensor coefficients and theta tensor regions

The qVFamily bad places determine a *dependent* tensor family: for each bad
place b, the tensor block is the one-factor block at the actual F-place
(nativeBadLift T).lift b and its own rational prime p_b.  There is no single
fixed p equal to all bad primes, so this is the actual per-b tensor index
(indexed by Bad), not a fake singleton fixed-p tensor.

For each b:

  c b = ((qVFamily T b).order : Real)  (the actual positive qVFamily order),
  thetaCoefficient j b = (gaussExponent j.1).toNat * c b.

The actual Theta tensor scaled region at label j is
thetaTensorScaledRegion (places b) (tuple b) (thetaCoefficient j b) from
ThetaTensorScaledImageActual.  All equalities are actual; no gap field.
No inequality/axiom/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamThetaImageActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual F-place lift of b. -/
abbrev qVFamTensorPlace : NumberField.FinitePlace T.arithmetic.F :=
  (nativeBadLift T).lift b

/-- The rational prime of the actual F-place. -/
noncomputable def qVFamTensorP : ℕ :=
  (completionRationalPrime (qVFamTensorPlace T b)).val

/-- The rational prime is prime. -/
noncomputable instance qVFamTensorPFact : Fact (Nat.Prime (qVFamTensorP T b)) := by
  unfold qVFamTensorP
  exact ⟨(completionRationalPrime (qVFamTensorPlace T b)).property⟩

/-- The one-factor tensor place index. -/
abbrev qVFamTensorV : Type := Unit

/-- The actual tensor places: the lift b at the unique factor. -/
noncomputable def qVFamTensorPlaces
    (_i : qVFamTensorV) (_a : Unit) :
    FinitePlaceAtPrime T.arithmetic.F (qVFamTensorP T b) :=
  ⟨qVFamTensorPlace T b, rfl⟩

/-- The actual tensor tuple: the unique point. -/
noncomputable def qVFamTensorTuple (_i : qVFamTensorV) : Unit := ()

/-- The actual one-factor tensor block at b. -/
abbrev qVFamTensorBlock : Type :=
  ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple

/-- The actual qVFamily order coefficient c b. -/
noncomputable def qVFamTensorCoefficient : Real :=
  ((qVFamily T b).order : Real)

/-- The coefficient is nonnegative. -/
theorem qVFamTensorCoefficient_nonneg :
    0 ≤ qVFamTensorCoefficient T b :=
  Nat.cast_nonneg _

/-- The coefficient is the actual order (and the positive exponent). -/
theorem qVFamTensorCoefficient_eq_order :
    qVFamTensorCoefficient T b = ((qVFamily T b).order : Real) := rfl

/-- The theta coefficient j b = j^2 * order. -/
noncomputable def qVFamThetaTensorCoefficient
    (j : SignedLabel l.value) : qVFamTensorV → Real :=
  fun _ => (gaussExponent j.1).toNat * qVFamTensorCoefficient T b

/-- Actual equality: theta coefficient = Gaussian exponent * qVFamily order. -/
theorem qVFamThetaTensorCoefficient_eq
    (j : SignedLabel l.value) :
    qVFamThetaTensorCoefficient T b j = fun _ =>
      ((gaussExponent j.1).toNat : Real) * qVFamTensorCoefficient T b := rfl

/-- The actual theta tensor scaled region at label j, using the same-source
qVFamily coefficient and the actual one-factor block at b. -/
noncomputable def qVFamThetaTensorRegion
    (j : SignedLabel l.value) : Set (qVFamTensorBlock T b) :=
  thetaTensorScaledRegion
    (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
    (qVFamThetaTensorCoefficient T b j)

/-- The region is exactly the thetaTensorScaledRegion from
ThetaTensorScaledImageActual. -/
theorem qVFamThetaTensorRegion_eq
    (j : SignedLabel l.value) :
    qVFamThetaTensorRegion T b j =
      thetaTensorScaledRegion
        (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
        (qVFamThetaTensorCoefficient T b j) := rfl

/-- Actual dependent tensor coefficient data over the bad family. -/
structure QVFamTensorCoefficientData where
  p : ℕ
  p_eq : p = qVFamTensorP T b
  places : (i : qVFamTensorV) → Unit →
    FinitePlaceAtPrime T.arithmetic.F (qVFamTensorP T b)
  places_eq : places = qVFamTensorPlaces T b
  tuple : (i : qVFamTensorV) → Unit
  tuple_eq : tuple = qVFamTensorTuple
  coefficient : Real
  coefficient_eq : coefficient = qVFamTensorCoefficient T b
  thetaCoefficient : SignedLabel l.value → qVFamTensorV → Real
  thetaCoefficient_eq : thetaCoefficient = qVFamThetaTensorCoefficient T b

/-- The actual tensor coefficient data at b. -/
noncomputable def qVFamTensorCoefficientData :
    QVFamTensorCoefficientData T b where
  p := qVFamTensorP T b
  p_eq := rfl
  places := qVFamTensorPlaces T b
  places_eq := rfl
  tuple := qVFamTensorTuple
  tuple_eq := rfl
  coefficient := qVFamTensorCoefficient T b
  coefficient_eq := rfl
  thetaCoefficient := qVFamThetaTensorCoefficient T b
  thetaCoefficient_eq := rfl

/-- Projection: the tensor coefficient is the qVFamily order. -/
theorem qVFamTensorCoefficientData_coefficient :
    (qVFamTensorCoefficientData T b).coefficient =
      ((qVFamily T b).order : Real) := rfl

end LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

end
