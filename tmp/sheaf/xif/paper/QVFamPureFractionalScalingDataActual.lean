import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # ArithmeticTuplePureFractionalScalingData from the qVFamily unit

For each bad place b, use the actual one-factor tensor block
qVFamTensorBlock T b (place lift b, rational prime p_b, tuple ()).

The actual qVFamily completion unit g = (qVFamily T b).q has norm in (0,1).
Choose the real coefficient

  c b = - logb (p_b) ||g||,

so that

  ||g|| = p_b ^ (-(c b)).

Then the production constructor arithmeticTuplePureFractionalScalingData_ofGenerator
fills the actual localGenerator, norm, commonExponent, integerExponent, localUnit,
unitTensor_action and integerTensor_mul_holomorphic fields.  No fake data:
every field comes from the actual qVFamily unit and the actual tensor block.

No inequality/axiom/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual qVFamily completion unit in the tensor place. -/
noncomputable def qVFamTensorGenerator :
    CommonPrimeCompletion
      ((qVFamTensorPlaces T b) () (qVFamTensorTuple ())) :=
  (qVFamily T b).q

/-- The actual coefficient c b = - logb(p_b) ||qVFamily||. -/
noncomputable def qVFamPureCoefficient :
    qVFamTensorV → Real :=
  fun _ => -Real.logb (qVFamTensorP T b : Real)
    ‖qVFamTensorGenerator T b‖

/-- The generator norm is exactly p_b^{-c}. -/
theorem qVFamTensorGenerator_norm :
    ‖qVFamTensorGenerator T b‖ =
      (qVFamTensorP T b : Real) ^ (-(qVFamPureCoefficient T b ())) := by
  unfold qVFamTensorGenerator qVFamPureCoefficient
  have hp_pos : (0 : Real) < (qVFamTensorP T b : Real) := by
    have hprime : Nat.Prime (qVFamTensorP T b) := by
      unfold qVFamTensorP
      exact (completionRationalPrime (qVFamTensorPlace T b)).property
    exact_mod_cast hprime.pos
  have hp_ne_one : (qVFamTensorP T b : Real) ≠ 1 := by
    have hprime : Nat.Prime (qVFamTensorP T b) := by
      unfold qVFamTensorP
      exact (completionRationalPrime (qVFamTensorPlace T b)).property
    exact ne_of_gt (by exact_mod_cast hprime.one_lt : (1 : Real) < (qVFamTensorP T b : Real))
  have hnorm_pos : 0 < ‖(qVFamily T b).q‖ :=
    norm_pos_iff.mpr (qVFamily T b).q_ne_zero
  rw [neg_neg]
  change ‖(qVFamily T b).q‖ =
    (qVFamTensorP T b : Real) ^ (-(-Real.logb (qVFamTensorP T b : Real)
      ‖(qVFamily T b).q‖))
  exact (Real.rpow_logb hp_pos hp_ne_one hnorm_pos).symm

/-- The actual pure fractional scaling data from the qVFamily completion unit. -/
noncomputable def qVFamPureFractionalScalingData :
    ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple (qVFamPureCoefficient T b) :=
  arithmeticTuplePureFractionalScalingData_ofGenerator
    (qVFamTensorPlaces T b) qVFamTensorTuple (qVFamPureCoefficient T b)
    (fun _ => qVFamTensorGenerator T b)
    (fun _ => qVFamTensorGenerator_norm T b)

/-- The local generator of the constructed data is the actual qVFamily unit. -/
theorem qVFamPureFractionalScalingData_localGenerator :
    (qVFamPureFractionalScalingData T b).localGenerator () =
      qVFamTensorGenerator T b := rfl

/-- The local generator norm formula. -/
theorem qVFamPureFractionalScalingData_localGenerator_norm :
    ‖(qVFamPureFractionalScalingData T b).localGenerator ()‖ =
      (qVFamTensorP T b : Real) ^ (-(qVFamPureCoefficient T b ())) :=
  (qVFamPureFractionalScalingData T b).localGenerator_norm ()

/-- The actual normalized log-volume of the scaled region is -(sum c) log p. -/
theorem qVFamPureFractionalScalingData_logVolume
    [MeasurableSpace (qVFamTensorBlock T b)]
    [BorelSpace (qVFamTensorBlock T b)]
    (mu : Measure (qVFamTensorBlock T b))
    [Measure.IsAddHaarMeasure mu] :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b)
        qVFamTensorTuple mu
        ((arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
            qVFamTensorTuple (qVFamPureCoefficient T b) *
          arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b)
            qVFamTensorTuple :
            Submodule ℤ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)) :
          Set (qVFamTensorBlock T b)) =
      -((∑ _ : qVFamTensorV, qVFamPureCoefficient T b _) *
        Real.log (qVFamTensorP T b : Real)) :=
  arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (qVFamPureFractionalScalingData T b)

end LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataActual

end
