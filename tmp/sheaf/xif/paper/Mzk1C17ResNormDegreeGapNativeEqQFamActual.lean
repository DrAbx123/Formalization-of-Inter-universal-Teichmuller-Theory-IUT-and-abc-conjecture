/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17ResidueOneConsumeActual
import tmp.sheaf.xif.paper.Mzk1C17ResNormDegreeGapOfResidueOneActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1C17ResNormDegreeGapNativeEqQFamActual

open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneConsumeActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneSinglePointActual
open LeanFormal.IUT.XiFPaper.Mzk1C17QCANDResNormComapActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
theorem localResidueDegree_native_eq_qVFam_of_log
    (b : Bad (nativePlaceSelection T))
    (hK : Real.log (residueNormBase (nativeBaseSectionPlace T b)) =
      Real.log (residueNormBase (comap (k := T.arithmetic.Fmod)
        (nativeBaseSectionPlace T b))))
    (hF : Real.log (residueNormBase (qVFamTensorPlace T b)) =
      Real.log (residueNormBase (comap (k := T.arithmetic.Fmod)
        (qVFamTensorPlace T b)))) :
    localResidueDegree (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b) =
      localResidueDegree (k := T.arithmetic.Fmod) (qVFamTensorPlace T b) := by
  rw [residueOne_nativeBase_of_log T b hK,
    (localResidueDegree_qVFam_eq_one_iff_log_residue_eq T b).mpr hF]


end LeanFormal.IUT.XiFPaper.Mzk1C17ResNormDegreeGapNativeEqQFamActual
