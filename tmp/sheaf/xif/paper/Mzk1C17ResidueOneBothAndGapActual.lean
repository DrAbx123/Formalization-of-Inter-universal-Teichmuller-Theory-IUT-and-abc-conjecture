/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17ResidueOneBothConsumeActual
import tmp.sheaf.xif.paper.Mzk1C17ResNormDegreeGapLogActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneBothAndGapActual

open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneBothConsumeActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResNormDegreeGapLogActual
open LeanFormal.IUT.XiFPaper.Mzk1C17QCANDResNormComapActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
theorem residueOne_both_and_resNormDegreeGap
    (hK : ∀ b : Bad (nativePlaceSelection T),
      Real.log (residueNormBase (nativeBaseSectionPlace T b)) =
        Real.log (residueNormBase (comap (k := T.arithmetic.Fmod)
          (nativeBaseSectionPlace T b))))
    (hF : ∀ b : Bad (nativePlaceSelection T),
      Real.log (residueNormBase (qVFamTensorPlace T b)) =
        Real.log (residueNormBase (comap (k := T.arithmetic.Fmod)
          (qVFamTensorPlace T b)))) :
    ResNormDegreeGap T :=
  resNormDegreeGap_of_log_residue_eq T hK hF


end LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneBothAndGapActual
