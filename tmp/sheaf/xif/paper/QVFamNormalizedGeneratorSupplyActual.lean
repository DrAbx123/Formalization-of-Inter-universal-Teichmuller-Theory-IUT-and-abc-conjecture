import tmp.sheaf.xif.paper.QVFamPureFractionalScalingDataGapActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers

/-!
# Actual normalized generator supply for the qVFamily tensor block

The qVFamily q lives in the default completion norm.  The normalized tensor
constructor needs a generator in CommonPrimeCompletion (the spectral norm) with
norm p ^ (-(c)).  This file uses the only actual normalization datum in the
tree: CommonPrimeCompletion is definitionally NormalizedCompletion, whose norm
is the spectral norm.  The qVFamily q is therefore coerced to that same
completed field, and its *normalized* coefficient

  c_norm = -logb_p ||q||_normalized

is used.  The norm identity p ^ (-(c_norm)) = ||q||_normalized is proved
directly by Real.rpow_logb, not assumed.

This gives an actual normalized generator supply and the actual pure fractional
scaling data at c_norm.  The remaining exact object-level gap is the equality
c_norm = qVFamPureCoefficient, whose latter coefficient was defined with the
default completion norm.  No tree theorem identifies the two norm instances on
the qVFamily element (only integer-ball equivalences are available), so this
equality is recorded as an explicit proposition and is not faked.

No sorry/axiom/True/PUnit, no inequality. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The qVFamily q as an element of the normalized CommonPrimeCompletion at its
actual tensor place. -/
noncomputable def qVFamNormalizedGenerator :
    CommonPrimeCompletion ((qVFamTensorPlaces T b) () ()) :=
  (qVFamily T b).q

/-- The normalized generator is the actual nonzero qVFamily q. -/
theorem qVFamNormalizedGenerator_ne_zero :
    qVFamNormalizedGenerator T b ≠ 0 :=
  (qVFamily T b).q_ne_zero

/-- The actual normalized coefficient: -logb_p of the normalized norm. -/
noncomputable def qVFamNormalizedCoefficient : Real :=
  -Real.logb (qVFamTensorP T b : Real)
    ‖qVFamNormalizedGenerator T b‖

/-- The normalized generator has norm p^{-(c_norm)}.  This is the actual
normalization identity, proved from the spectral norm and Real.rpow_logb. -/
theorem qVFamNormalizedGenerator_norm :
    ‖qVFamNormalizedGenerator T b‖ =
      (qVFamTensorP T b : Real) ^ (-(qVFamNormalizedCoefficient T b)) := by
  have hprime : Nat.Prime (qVFamTensorP T b) :=
    Fact.out (p := Nat.Prime (qVFamTensorP T b))
  have hp1 : (1 : Real) < (qVFamTensorP T b : Real) := by
    exact_mod_cast hprime.one_lt
  have hp0 : (0 : Real) < (qVFamTensorP T b : Real) :=
    lt_trans zero_lt_one hp1
  have hne : (qVFamTensorP T b : Real) ≠ 1 := ne_of_gt hp1
  have hnorm : 0 < ‖qVFamNormalizedGenerator T b‖ :=
    norm_pos_iff.mpr (qVFamNormalizedGenerator_ne_zero T b)
  unfold qVFamNormalizedCoefficient
  rw [neg_neg]
  exact (Real.rpow_logb hp0 hne hnorm).symm

/-- An actual normalized generator supply at a specified coefficient. -/
structure NormalizedGeneratorSupplyAt (c : Real) where
  generator : CommonPrimeCompletion ((qVFamTensorPlaces T b) () ())
  generator_norm : ‖generator‖ = (qVFamTensorP T b : Real) ^ (-(c))

/-- The normalized qVFamily generator has normalized spectral norm < 1,
transported from the actual qVFamily default norm < 1 by the proved integer-ball
norm comparison. -/
theorem qVFamNormalizedGenerator_norm_lt_one :
    ‖qVFamNormalizedGenerator T b‖ < 1 := by
  have hq : ‖(qVFamily T b).q‖ < 1 :=
    qNorm_lt_one (qVFamily T b)
  have hdefault :
      ‖normalizedCompletionRingEquiv
        ((qVFamTensorPlaces T b) () ()).val
        (qVFamNormalizedGenerator T b)‖ < 1 := by
    change ‖(qVFamily T b).q‖ < 1
    exact hq
  exact (normalizedCompletion_norm_lt_one_iff
    ((qVFamTensorPlaces T b) () ()).val (qVFamNormalizedGenerator T b)).mp hdefault

/-- The actual normalized coefficient is positive: the normalized qVFamily norm
is < 1, so its p-logb is negative and the coefficient is its negative. -/
theorem qVFamNormalizedCoefficient_pos :
    0 < qVFamNormalizedCoefficient T b := by
  have hprime : Nat.Prime (qVFamTensorP T b) :=
    Fact.out (p := Nat.Prime (qVFamTensorP T b))
  have hp1 : (1 : Real) < (qVFamTensorP T b : Real) := by
    exact_mod_cast hprime.one_lt
  have hnorm_pos : 0 < ‖qVFamNormalizedGenerator T b‖ :=
    norm_pos_iff.mpr (qVFamNormalizedGenerator_ne_zero T b)
  have hnorm_lt : ‖qVFamNormalizedGenerator T b‖ < 1 :=
    qVFamNormalizedGenerator_norm_lt_one T b
  unfold qVFamNormalizedCoefficient
  exact neg_pos.mpr (Real.logb_neg hp1 hnorm_pos hnorm_lt)

/-- The supply-version normalized coefficient is nonnegative. -/
theorem qVFamNormalizedCoefficient_nonneg :
    0 ≤ qVFamNormalizedCoefficient T b :=
  le_of_lt (qVFamNormalizedCoefficient_pos T b)

/-- The actual normalized generator supply at the normalized coefficient. -/
noncomputable def qVFamNormalizedGeneratorSupplyAt :
    NormalizedGeneratorSupplyAt T b (qVFamNormalizedCoefficient T b) where
  generator := qVFamNormalizedGenerator T b
  generator_norm := qVFamNormalizedGenerator_norm T b

/-- The normalized coefficient as a constant family over the one tensor factor. -/
noncomputable def qVFamNormalizedCoefficientFamily :
    qVFamTensorV → Real :=
  fun _ => qVFamNormalizedCoefficient T b

/-- The actual pure fractional scaling data at the normalized coefficient. -/
noncomputable def qVFamNormalizedPureFractionalScalingData :
    ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (qVFamNormalizedCoefficientFamily T b) :=
  arithmeticTuplePureFractionalScalingData_ofGenerator
    (qVFamTensorPlaces T b) qVFamTensorTuple
    (qVFamNormalizedCoefficientFamily T b)
    (fun _ => qVFamNormalizedGenerator T b)
    (fun _ => qVFamNormalizedGenerator_norm T b)

/-- Exact object-level norm-coefficient gap: the normalized coefficient equals
the default-norm qVFamPureCoefficient. -/
def QVFamNormalizedCoefficientGap : Prop :=
  qVFamNormalizedCoefficient T b = qVFamPureCoefficient T b ()

/-- Conditional actual NormalizedGeneratorSupply for the default-norm
coefficient, using the exact coefficient equality. -/
noncomputable def qVFamNormalizedGeneratorSupply_of_coefficient_eq
    (h : qVFamNormalizedCoefficient T b = qVFamPureCoefficient T b ()) :
    NormalizedGeneratorSupply T b where
  generator := qVFamNormalizedGenerator T b
  generator_norm := by
    rw [← h]
    exact qVFamNormalizedGenerator_norm T b

/-- The actual qVFamily generator in the normalized completion. -/
theorem qVFamNormalizedGenerator_eq :
    qVFamNormalizedGenerator T b = (qVFamily T b).q := rfl

/-- The normalized coefficient is the negative logb_p of the normalized norm. -/
theorem qVFamNormalizedCoefficient_eq :
    qVFamNormalizedCoefficient T b =
      -Real.logb (qVFamTensorP T b : Real)
        ‖qVFamNormalizedGenerator T b‖ := rfl

end LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
