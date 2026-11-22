/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17ResidueOneConsumeActual
import tmp.sheaf.xif.paper.Mzk1C17ResidueOneBothSidesActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneBothConsumeActual

open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneConsumeActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneBothSidesActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
theorem residueOne_both_of_log
    (hK : ∀ b : Bad (nativePlaceSelection T),
      Real.log (residueNormBase (nativeBaseSectionPlace T b)) =
        Real.log (residueNormBase (comap (k := T.arithmetic.Fmod)
          (nativeBaseSectionPlace T b))))
    (hF : ∀ b : Bad (nativePlaceSelection T),
      Real.log (residueNormBase (qVFamTensorPlace T b)) =
        Real.log (residueNormBase (comap (k := T.arithmetic.Fmod)
          (qVFamTensorPlace T b)))) :
    (∀ b : Bad (nativePlaceSelection T),
      localResidueDegree (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b) = 1) ∧
    (∀ b : Bad (nativePlaceSelection T),
      localResidueDegree (k := T.arithmetic.Fmod) (qVFamTensorPlace T b) = 1) :=
  ⟨fun b => residueOne_nativeBase_of_log T b (hK b),
   fun b => residueOne_qVFam_of_log T b (hF b)⟩


end LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneBothConsumeActual
