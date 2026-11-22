/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17ResidueOneBothSidesActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneConsumeActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneBothSidesActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneSinglePointActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
theorem residueOne_nativeBase_of_log
    (b : Bad (nativePlaceSelection T))
    (h : Real.log (residueNormBase (nativeBaseSectionPlace T b)) =
      Real.log (residueNormBase (comap (k := T.arithmetic.Fmod)
        (nativeBaseSectionPlace T b)))) :
    localResidueDegree (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b) = 1 :=
  localResidueDegree_eq_one_of_log_residue_eq T b h
theorem residueOne_qVFam_of_log
    (b : Bad (nativePlaceSelection T))
    (h : Real.log (residueNormBase (qVFamTensorPlace T b)) =
      Real.log (residueNormBase (comap (k := T.arithmetic.Fmod)
        (qVFamTensorPlace T b)))) :
    localResidueDegree (k := T.arithmetic.Fmod) (qVFamTensorPlace T b) = 1 :=
  (localResidueDegree_qVFam_eq_one_iff_log_residue_eq T b).mpr h
end LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneConsumeActual
