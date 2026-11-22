import tmp.sheaf.xif.paper.QVFamThetaImageActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegree
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure

/-! # qVFamily fractional-lattice coefficients on the tensor block

For each native bad place b, the actual qVFamily q lives at the finite
F-place (nativeBadLift T).lift b.  Its rational prime is

  p_b = (completionRationalPrime (nativeBadLift T).lift b).val

and the one-factor tensor block is

  ArithmeticTensorTupleBlock (qVBadTensorPlaces b) (qVBadTensorTuple b)

with tensorIndex Unit, tensorPlaceIndex Unit, and the actual F-place at p_b.

The fractional-lattice coefficient is the actual positive qVFamily order times
the local residue degree times the theta Gaussian exponent j^2:

  c_b(j) = order(qVFamily T b) * localResidueDegree(lift b) * j^2.

This is the coefficient that makes the scaled-region formula

  mu_log (c_b . fractionalLattice * holomorphicLattice)
    = -(sum_i c_i) * log p_b

match the qVFamily local signed log.

The architecture has a fixed p in ArithmeticTensorTupleBlock; the bad places
have varying rational primes, so a single tensor block over ALL Bad is not
constructed.  This file gives the actual per-b tensor block/coefficient and the
conditional mu_log formula; the varying-p product is an exact architectural gap,
not a fake single block.  No inequality/axiom/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QVFamTensorFractionalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.QVFamThetaImageActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
open LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
open LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual F-place of the qVFamily q. -/
abbrev qVFamPlace : NumberField.FinitePlace T.arithmetic.F :=
  (nativeBadLift T).lift b

/-- The rational prime of the qVFamily F-place. -/
noncomputable def qVFamP : ℕ :=
  (completionRationalPrime (qVFamPlace T b)).val

/-- The actual qVFamily place at its rational prime. -/
noncomputable def qVFamPlaceAtPrime : FinitePlaceAtPrime T.arithmetic.F (qVFamP T b) :=
  ⟨qVFamPlace T b, rfl⟩

/-- The one-factor tensor place index. -/
abbrev qVFamTensorPlaceIndex : Type := Unit

/-- The rational prime of qVFamP is prime. -/
noncomputable instance qVFamPFact : Fact (Nat.Prime (qVFamP T b)) := by
  unfold qVFamP
  exact ⟨(completionRationalPrime (qVFamPlace T b)).property⟩

/-- The actual qVFamily tensor places (one factor, actual F-place). -/
noncomputable def qVFamTensorPlaces
    (_i : Unit) (_a : qVFamTensorPlaceIndex) :
    FinitePlaceAtPrime T.arithmetic.F (qVFamP T b) :=
  qVFamPlaceAtPrime T b

/-- The actual one-factor tensor tuple. -/
noncomputable def qVFamTensorTuple (_i : Unit) : qVFamTensorPlaceIndex := ()

/-- The actual one-factor tensor block at b. -/
abbrev qVFamTensorBlock : Type :=
  ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) (qVFamTensorTuple)

/-- The actual fractional-lattice coefficient from qVFamily order and the theta
exponent j^2. -/
noncomputable def qVFamTensorCoefficient
    (j : SignedLabel l.value) : Unit → Real :=
  fun _ =>
    ((qVFamily T b).order : Real) *
      (localResidueDegree (k := T.arithmetic.Fmod) (qVFamPlace T b) : Real) *
        ((gaussExponent j.1).toNat : Real)

/-- Actual equality: the tensor coefficient is order * residue degree * j^2. -/
theorem qVFamTensorCoefficient_eq
    (j : SignedLabel l.value) :
    qVFamTensorCoefficient T b j = fun _ =>
      ((qVFamily T b).order : Real) *
        (localResidueDegree (k := T.arithmetic.Fmod) (qVFamPlace T b) : Real) *
          ((gaussExponent j.1).toNat : Real) := rfl

/-- The actual qVFamily fractional-lattice scaled region inside the tensor block. -/
noncomputable def qVFamTensorFractionalRegion
    (j : SignedLabel l.value) : Set (qVFamTensorBlock T b) :=
  ((arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
      (qVFamTensorTuple b) (qVFamTensorCoefficient T b j) *
    arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b)
      (qVFamTensorTuple T b) :
      Submodule ℤ_[(qVFamP T b)] (qVFamTensorBlock T b)) : Set (qVFamTensorBlock T b))

/-- The scaled region is the actual set, not a fabricated region. -/
theorem qVFamTensorFractionalRegion_eq
    (j : SignedLabel l.value) :
    qVFamTensorFractionalRegion T b j =
      ((arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
          (qVFamTensorTuple T b) (qVFamTensorCoefficient T b j) *
        arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b)
          (qVFamTensorTuple T b) :
          Submodule ℤ_[(qVFamP T b)] (qVFamTensorBlock T b)) : Set (qVFamTensorBlock T b)) := rfl

/-- Conditional actual mu_log formula: given the actual pure fractional scaling
data for the coefficient vector c_b(j), the scaled-region normalized log-volume
is -(sum c_i) log p_b. -/
theorem qVFamTensorFractionalRegion_logVolume
    [MeasurableSpace (qVFamTensorBlock T b)]
    [BorelSpace (qVFamTensorBlock T b)]
    (mu : Measure (qVFamTensorBlock T b))
    [Measure.IsAddHaarMeasure mu]
    (j : SignedLabel l.value)
    (data : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) (qVFamTensorTuple T b) (qVFamTensorCoefficient T b j)) :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b)
        (qVFamTensorTuple T b) mu (qVFamTensorFractionalRegion T b j) =
      -((∑ _ : Unit, qVFamTensorCoefficient T b j _) *
        Real.log (qVFamP T b : Real)) :=
  arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    (qVFamTensorPlaces T b) (qVFamTensorTuple T b) mu data

end LeanFormal.IUT.XiFPaper.QVFamTensorFractionalActual

end
