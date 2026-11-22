/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17ResNormDegreeGapOfResidueOneActual
import tmp.sheaf.xif.paper.Mzk1C17ResidueOneSinglePointActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.Mzk1C17ResNormDegreeGapLogActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1C17QCANDResNormComapActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneSinglePointActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResNormDegreeGapOfResidueOneActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
theorem resNormDegreeGap_of_log_residue_eq
    (hK : ∀ b : Bad (nativePlaceSelection T),
      Real.log (residueNormBase (nativeBaseSectionPlace T b)) =
        Real.log (residueNormBase (comap (k := T.arithmetic.Fmod)
          (nativeBaseSectionPlace T b))))
    (hF : ∀ b : Bad (nativePlaceSelection T),
      Real.log (residueNormBase (qVFamTensorPlace T b)) =
        Real.log (residueNormBase (comap (k := T.arithmetic.Fmod)
          (qVFamTensorPlace T b)))) :
    ResNormDegreeGap T := by
  apply resNormDegreeGap_of_residueOne
  · intro b; exact localResidueDegree_eq_one_of_log_residue_eq T b (hK b)
  · intro b
    exact (localResidueDegree_qVFam_eq_one_iff_log_residue_eq T b).mpr (hF b)
end LeanFormal.IUT.XiFPaper.Mzk1C17ResNormDegreeGapLogActual
