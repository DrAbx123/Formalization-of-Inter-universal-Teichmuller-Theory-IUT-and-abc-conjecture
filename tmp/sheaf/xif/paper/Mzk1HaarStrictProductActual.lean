/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HaarStrictChainSummaryActual

/-! # A596/A605 hull 收尾: `Mzk1HaarStrictProductActual` thin re-export

The strict-measure proof is in the GREEN `Mzk1HaarStrictChainSummaryActual` /
`Mzk1HaarStrictScalingProductActual`; this module re-exports the resolved interface
under the old name; no named `strict_measure` is left. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HaarStrictProductActual

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

theorem product_haarStrict :
    rootExtensionProductHaar T (rpRegion T) <
      rootExtensionProductHaar T (s1902Hull T) :=
  strictChain_product (T := T)

theorem product_strict_measure :
    rpVolume T (rpRegion T) < rpVolume T (s1902Hull T) :=
  strictChain_strict_measure (T := T)

theorem product_cor312 (hqneg : requirementSignedQ (rpRequirement T) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (rpRequirement T) hqneg ipl hipl she hshe apt hapt) :=
  strictChain_cor312 (T := T) hqneg ipl hipl she hshe apt hapt

def productRows : List (String × String × String) :=
  [ ("strict Haar", "strictChain_product", "GREEN"),
    ("strict_measure", "strictChain_strict_measure", "GREEN (theorem)"),
    ("scope", "conditional Cor312Conclusion; no ABC closure", "INTEGRITY") ]

theorem productRows_length : productRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1HaarStrictProductActual

end