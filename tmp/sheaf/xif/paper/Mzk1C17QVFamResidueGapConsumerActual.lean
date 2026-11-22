/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17BothResidueFieldInputsGapActual
import tmp.sheaf.xif.paper.Mzk1C17ResNormDegreeGapLogActual
import tmp.sheaf.xif.paper.Mzk1C17QCANDResNormComapActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.Mzk1C17QVFamResidueGapConsumerActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1C17BothResidueFieldInputsGapActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResNormDegreeGapLogActual
open LeanFormal.IUT.XiFPaper.Mzk1C17QCANDResNormComapActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneSinglePointActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
theorem log_residue_qVFam_eq_of_residueFieldEquiv
    (hF : QVFamResidueFieldEquivInput T)
    (b : Bad (nativePlaceSelection T)) :
    Real.log (residueNormBase (qVFamTensorPlace T b)) =
      Real.log (residueNormBase (comap (k := T.arithmetic.Fmod)
        (qVFamTensorPlace T b))) := by
  have hf : localResidueDegree (k := T.arithmetic.Fmod) (qVFamTensorPlace T b) = 1 := by
    change Ideal.inertiaDeg'
      (comap (k := T.arithmetic.Fmod) (qVFamTensorPlace T b)).maximalIdeal.asIdeal
      (qVFamTensorPlace T b).maximalIdeal.asIdeal = 1
    exact inertiaDeg'_eq_one_of_residueFieldEquiv (hF b)
  rw [log_residue_nativeF_eq_degree_mul, hf]
  norm_num
theorem resNormDegreeGap_of_nativeBaseLog_and_qVFamInput
    (hK : ∀ b : Bad (nativePlaceSelection T),
      Real.log (residueNormBase (nativeBaseSectionPlace T b)) =
        Real.log (residueNormBase (comap (k := T.arithmetic.Fmod)
          (nativeBaseSectionPlace T b))))
    (hF : QVFamResidueFieldEquivInput T) :
    ResNormDegreeGap T :=
  resNormDegreeGap_of_log_residue_eq T hK
    (fun b => log_residue_qVFam_eq_of_residueFieldEquiv T hF b)
end LeanFormal.IUT.XiFPaper.Mzk1C17QVFamResidueGapConsumerActual
