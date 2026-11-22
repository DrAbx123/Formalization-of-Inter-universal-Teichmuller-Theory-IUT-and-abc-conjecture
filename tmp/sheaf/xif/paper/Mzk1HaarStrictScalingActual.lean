/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HaarStrictChainSummaryActual

/-! # A596/A605 hull 收尾: `Mzk1HaarStrictScalingActual` thin re-export

The strict-measure proofs live in the GREEN self-contained files; this module only
re-exports them under the old names (no new mathematics, no named `strict_measure`). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HaarStrictScalingActual

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

/-- 1D strict ball measure (re-export). -/
theorem scaling_oneDim_strict (b : Bad (nativePlaceSelection T)) (R : Real) (hR : 0 < R) :
    rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
        (R / (qVFamTensorP T b : Real))) <
      rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b) R) :=
  strictChain_1d (T := T) b R hR

/-- Product strict Haar increase (re-export). -/
theorem scaling_haarStrict :
    rootExtensionProductHaar T (rpRegion T) <
      rootExtensionProductHaar T (s1902Hull T) :=
  strictChain_product (T := T)

/-- Strict measure as a theorem (re-export). -/
theorem scaling_strict_measure :
    rpVolume T (rpRegion T) < rpVolume T (s1902Hull T) :=
  strictChain_strict_measure (T := T)

/-- Conditional Cor312 conclusion (re-export). -/
theorem scaling_cor312 (hqneg : requirementSignedQ (rpRequirement T) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (rpRequirement T) hqneg ipl hipl she hshe apt hapt) :=
  strictChain_cor312 (T := T) hqneg ipl hipl she hshe apt hapt

def scalingRows : List (String × String × String) :=
  [ ("1D strict ball measure", "strictChain_1d", "GREEN"),
    ("product strict Haar", "strictChain_product", "GREEN"),
    ("strict_measure", "strictChain_strict_measure", "GREEN (theorem)"),
    ("Cor312Conclusion", "strictChain_cor312", "GREEN (conditional on hqneg/evidence)") ]

theorem scalingRows_length : scalingRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1HaarStrictScalingActual

end