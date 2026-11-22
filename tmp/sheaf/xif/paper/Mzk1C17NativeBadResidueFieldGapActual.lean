/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17ResidueWeightChainActual
import tmp.sheaf.xif.paper.Mzk1C17ResidueFieldEquivActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1C17NativeBadResidueFieldGapActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResidueFieldEquivActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResidueWeightChainActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
def MissingNativeBadResidueFieldEquiv : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    ResidueFieldEquiv
      (p := (comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.asIdeal)
      (P := (nativeBadToKPlace T b).maximalIdeal.asIdeal)
theorem nativeBadLocalWeight_eq_one_of_missing
    (b : Bad (nativePlaceSelection T))
    (hfinite : Module.Finite
      ((comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.adicCompletionIntegers
        T.arithmetic.Fmod)
      ((nativeBadToKPlace T b).maximalIdeal.adicCompletionIntegers T.arithmetic.K))
    (hagree : localDataAgreesWithPlaceData (k := T.arithmetic.Fmod) (nativeBadToKPlace T b))
    (hunram : relativeRamificationIndex (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1)
    (hmissing : MissingNativeBadResidueFieldEquiv T) :
    nativeBadLocalWeight T b = 1 :=
  nativeBadLocalWeight_eq_one_of_residueFieldEquiv T b hfinite hagree hunram (hmissing b)


end LeanFormal.IUT.XiFPaper.Mzk1C17NativeBadResidueFieldGapActual
