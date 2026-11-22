/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17ResidueOneBothSidesActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneBothLogIffActual

open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneBothSidesActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneSinglePointActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
theorem residueOne_both_iff_log_both :
    (((∀ b : Bad (nativePlaceSelection T),
        localResidueDegree (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b) = 1) ∧
      (∀ b : Bad (nativePlaceSelection T),
        localResidueDegree (k := T.arithmetic.Fmod) (qVFamTensorPlace T b) = 1)) ↔
    ((∀ b : Bad (nativePlaceSelection T),
        Real.log (residueNormBase (nativeBaseSectionPlace T b)) =
          Real.log (residueNormBase (comap (k := T.arithmetic.Fmod)
            (nativeBaseSectionPlace T b)))) ∧
      (∀ b : Bad (nativePlaceSelection T),
        Real.log (residueNormBase (qVFamTensorPlace T b)) =
          Real.log (residueNormBase (comap (k := T.arithmetic.Fmod)
            (qVFamTensorPlace T b)))))) := by
  constructor
  · rintro ⟨hK, hF⟩
    exact ⟨fun b => (residueOne_nativeBase_iff_log T b).mp (hK b),
      fun b => (residueOne_qVFam_iff_log T b).mp (hF b)⟩
  · rintro ⟨hK, hF⟩
    exact ⟨fun b => (residueOne_nativeBase_iff_log T b).mpr (hK b),
      fun b => (residueOne_qVFam_iff_log T b).mpr (hF b)⟩


end LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneBothLogIffActual
