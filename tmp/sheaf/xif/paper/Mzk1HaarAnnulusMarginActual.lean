/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HaarStrictChainSummaryActual

/-! # A596/A605 hull 收尾: `Mzk1HaarAnnulusMarginActual` thin re-export

The margin-ball/ultrametric route is superseded by the GREEN product strictness;
this module re-exports the resulting strict measure under the old name. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HaarAnnulusMarginActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictScalingProductActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312RequirementResolvedActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictChainSummaryActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

theorem annulus_haarStrict :
    rootExtensionProductHaar T (rpRegion T) <
      rootExtensionProductHaar T (s1902Hull T) :=
  strictChain_product (T := T)

theorem annulus_strict_measure :
    rpVolume T (rpRegion T) < rpVolume T (s1902Hull T) :=
  strictChain_strict_measure (T := T)

def annulusRows : List (String × String × String) :=
  [ ("annulus/product strict Haar", "strictChain_product", "GREEN"),
    ("strict_measure", "strictChain_strict_measure", "GREEN (theorem)"),
    ("scope", "thin re-export; margin route superseded", "INTEGRITY") ]

theorem annulusRows_length : annulusRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1HaarAnnulusMarginActual

end