/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17NativeBadResidueFieldGapActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1C17NativeBadWeightApplyActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1C17NativeBadResidueFieldGapActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
def NativeBadWeightInputs : Prop :=
  (∀ b : Bad (nativePlaceSelection T),
    Module.Finite
      ((comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.adicCompletionIntegers
        T.arithmetic.Fmod)
      ((nativeBadToKPlace T b).maximalIdeal.adicCompletionIntegers T.arithmetic.K)) ∧
  (∀ b : Bad (nativePlaceSelection T),
    localDataAgreesWithPlaceData (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)) ∧
  (∀ b : Bad (nativePlaceSelection T),
    relativeRamificationIndex (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1)
theorem nativeBadLocalWeight_eq_one_of_inputs
    (H : NativeBadWeightInputs T)
    (hmissing : MissingNativeBadResidueFieldEquiv T) :
    ∀ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b = 1 :=
  fun b => nativeBadLocalWeight_eq_one_of_missing T b (H.1 b) (H.2.1 b) (H.2.2 b) hmissing


end LeanFormal.IUT.XiFPaper.Mzk1C17NativeBadWeightApplyActual
