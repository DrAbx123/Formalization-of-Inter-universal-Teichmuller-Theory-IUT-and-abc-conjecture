/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17ResNormDegreeGapOfResidueOneActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneWitnessActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1C17QCANDResNormComapActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResNormDegreeGapOfResidueOneActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
def ResidueOneArithmeticInput : Prop :=
  (∀ b : Bad (nativePlaceSelection T),
      localResidueDegree (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b) = 1) ∧
    (∀ b : Bad (nativePlaceSelection T),
      localResidueDegree (k := T.arithmetic.Fmod) (qVFamTensorPlace T b) = 1)
theorem resNormDegreeGap_of_residueOneArithmeticInput
    (h : ResidueOneArithmeticInput T) : ResNormDegreeGap T :=
  resNormDegreeGap_of_residueOne T h.1 h.2
end LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneWitnessActual
