import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import LeanFormal.IUT.Foundations.LocalFields.PadicFractionalLattice
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Actual tensor lambda from the qVFamily completion unit

The qVFamily q_v determines the actual local element

  qVFamLambdaLocal b = (qVFamily T b).q

in the selected CommonPrimeCompletion.  With the actual coefficient

  c b = -logb_{p_b} ||qVFamLambdaLocal b||,

its normalized norm is exactly p_b^{-c}, so qVFamLambdaLocal is an actual
fractional-lattice element.  The pure tensor

  qVFamTensorLambda = tensor_over_i qVFamLambdaLocal

is an actual element of qVFamTensorBlock, and it lies in the actual fractional
lattice F(c).

The production constructor arithmeticTuplePureFractionalScalingData_ofGenerator
gives the actual data (localGenerator, norm, integer exponents, local units,
integerTensor_mul_holomorphic), and the normalized log-volume formula gives

  mu_log(F(c) * O_hol) = -(sum c) log p.

No fake data; no inequality. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QVFamTensorLambdaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
open LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
open LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual qVFamily local generator in the selected CommonPrimeCompletion. -/
noncomputable def qVFamLambdaLocal :
    CommonPrimeCompletion
      ((qVFamTensorPlaces T b) () (qVFamTensorTuple ())) :=
  (qVFamily T b).q

/-- The actual coefficient c b = -logb_p ||qVFamLambdaLocal||. -/
noncomputable def qVFamLambdaCoefficient : qVFamTensorV → Real :=
  fun _ => -Real.logb (qVFamTensorP T b : Real) ‖qVFamLambdaLocal T b‖

/-- Actual local norm relation: ||lambda_local|| = p^{-c}. -/
theorem qVFamLambdaLocal_norm :
    ‖qVFamLambdaLocal T b‖ =
      (qVFamTensorP T b : Real) ^ (-(qVFamLambdaCoefficient T b ())) := by
  unfold qVFamLambdaLocal qVFamLambdaCoefficient
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
  exact (Real.rpow_logb hp_pos hp_ne_one hnorm_pos).symm

/-- The actual local generator lies in the fractional norm ball F(c). -/
theorem qVFamLambdaLocal_mem_fractionalLattice :
    qVFamLambdaLocal T b ∈
      padicFractionalLattice
        (p := qVFamTensorP T b)
        (K := CommonPrimeCompletion
          ((qVFamTensorPlaces T b) () (qVFamTensorTuple ())))
        (qVFamLambdaCoefficient T b ()) := by
  rw [mem_padicFractionalLattice_iff]
  rw [qVFamLambdaLocal_norm]

/-- The actual pure tensor lambda in the tensor block. -/
noncomputable def qVFamTensorLambda : qVFamTensorBlock T b :=
  finitePadicTensorTprod (p := qVFamTensorP T b)
    (fun _ : qVFamTensorV =>
      CommonPrimeCompletion
        ((qVFamTensorPlaces T b) () (qVFamTensorTuple ())))
    (fun _ => qVFamLambdaLocal T b)

/-- The lambda element lies in the actual fractional lattice F(c). -/
theorem qVFamTensorLambda_mem_fractionalLattice :
    qVFamTensorLambda T b ∈
      arithmeticTupleFractionalLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple
        (qVFamLambdaCoefficient T b) :=
  arithmeticTupleFractionalLattice_pure_tensor_mem
    (qVFamTensorPlaces T b) qVFamTensorTuple
    (qVFamLambdaCoefficient T b)
    (fun _ => qVFamLambdaLocal T b)
    (fun _ => qVFamLambdaLocal_mem_fractionalLattice T b)

/-- The actual pure fractional scaling data from the qVFamily local generator. -/
noncomputable def qVFamLambdaScalingData :
    ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (qVFamLambdaCoefficient T b) :=
  arithmeticTuplePureFractionalScalingData_ofGenerator
    (qVFamTensorPlaces T b) qVFamTensorTuple
    (qVFamLambdaCoefficient T b)
    (fun _ => qVFamLambdaLocal T b)
    (fun _ => qVFamLambdaLocal_norm T b)

/-- The normalized log-volume of the scaled region is -(sum c) log p. -/
theorem qVFamTensorLambda_scaledLogVolume
    [MeasurableSpace (qVFamTensorBlock T b)]
    [BorelSpace (qVFamTensorBlock T b)]
    (mu : Measure (qVFamTensorBlock T b))
    [Measure.IsAddHaarMeasure mu] :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b)
        qVFamTensorTuple mu
        ((arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
            qVFamTensorTuple (qVFamLambdaCoefficient T b) *
          arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b)
            qVFamTensorTuple :
            Submodule ℤ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)) :
          Set (qVFamTensorBlock T b)) =
      -((∑ _ : qVFamTensorV, qVFamLambdaCoefficient T b _) *
        Real.log (qVFamTensorP T b : Real)) :=
  arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (qVFamLambdaScalingData T b)

end LeanFormal.IUT.XiFPaper.QVFamTensorLambdaActual

end
