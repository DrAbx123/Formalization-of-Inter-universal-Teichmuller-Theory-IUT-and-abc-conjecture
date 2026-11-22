/- R2 A2: actual F-side generator/scaling datum for actualRootCoeff from urRootAlpha.

No fake NumberField: the generator is the actual root `urRootAlpha` in rootNormedExtension;
its Kummer power, nonvanishing, coefficient formula and Haar volume formula are derived from
urRootAlpha_pow/urRootAlpha_mass/ur_alpha_log_norm_eq and ur_cNorm_eq_localNormOrder.
-/
import tmp.sheaf.xif.paper.Mzk1G1F2R2LocalStepVActual
import tmp.sheaf.xif.paper.Mzk1URQNormalizationActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import Mathlib.Tactic
noncomputable section
open MeasureTheory
open scoped Pointwise
namespace LeanFormal.IUT.XiFPaper.FsideGeneratorTransportActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootExtensionActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootExtInstancesActual
open LeanFormal.IUT.XiFPaper.Mzk1URQNormalizationActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F2R2LocalStepVActual
open LeanFormal.IUT.LocalFieldLogarithm
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual F-side root generator in the finite root extension. -/
noncomputable def fsideRootGenerator : rootNormedExtension T b :=
  (show rootNormedExtension T b from urRootAlpha T b)

theorem fsideRootGenerator_ne_zero : fsideRootGenerator (T := T) (b := b) ≠ 0 :=
  urRootAlpha_ne_zero T b

/-- Actual Kummer power relation r^(2l)=q for the F-side generator. -/
theorem fsideRootGenerator_pow :
    (fsideRootGenerator (T := T) (b := b)) ^ (2 * l.value) =
      algebraMap (rootBase T b) (rootNormedExtension T b)
        ((sourceRootQUnit T b : rootBase T b)) :=
  urRootAlpha_pow T b

/-- The actual root coefficient is (1/(2l)) times the actual q-order. -/
theorem actualRootCoeff_eq_half_order :
    actualRootCoeff (l := l) T b () =
      (1 / (2 * (l.value : Real))) *
        localNormOrder (qVFamTensorP T b) ((sourceRootQUnit T b : rootBase T b)) := by
  unfold actualRootCoeff
  rw [ur_cNorm_eq_localNormOrder]
  ring

/-- Exact Haar volume formula for the actual generator translate, in terms of
actualRootCoeff and log p. -/
theorem fsideVolumeFormula
    (mu : Measure (rootNormedExtension T b)) [Measure.IsAddHaarMeasure mu]
    [Measure.Regular mu] :
    (1 / (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : Real)) *
      (Real.log (mu ((fsideRootGenerator (T := T) (b := b)) •
          (Integers (rootNormedExtension T b) : Set (rootNormedExtension T b)))).toReal -
        Real.log (mu (Integers (rootNormedExtension T b) :
          Set (rootNormedExtension T b))).toReal) =
      -actualRootCoeff (l := l) T b () * Real.log (qVFamTensorP T b : Real) := by
  rw [ulNormalizedLogMass_smul (p := qVFamTensorP T b) mu
    (fsideRootGenerator (T := T) (b := b)) (fsideRootGenerator_ne_zero (T := T) (b := b))]
  rw [ur_alpha_log_norm_eq, urRootQ_log_norm_order]
  rw [actualRootCoeff_eq_half_order]
  ring

#print axioms fsideRootGenerator_pow
#print axioms actualRootCoeff_eq_half_order
#print axioms fsideVolumeFormula
end LeanFormal.IUT.XiFPaper.FsideGeneratorTransportActual