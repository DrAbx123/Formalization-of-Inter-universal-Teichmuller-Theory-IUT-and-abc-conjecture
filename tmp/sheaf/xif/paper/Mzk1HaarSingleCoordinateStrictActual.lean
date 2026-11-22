/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HaarStrictChainSummaryActual

/-! # A577 hull (retired -> thin re-export): single-coordinate strict_measure

The construction of `strict_measure` is already fully proved by the green
`Mzk1HaarStrictChainSummaryActual` chain (1D p-scaling strict ball measure ->
product strict Haar increase -> `strictChain_strict_measure`).  This file is kept
only as a thin, stable re-export of that chain; it no longer duplicates the 1D
proof (whose old private lemmas were removed).

No sorry/axiom; no canonical change. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HaarSingleCoordinateStrictActual

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
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictScalingProductActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312RequirementResolvedActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictChainSummaryActual
open MeasureTheory
open scoped Pointwise ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- 1D p-scaling strict ball measure (re-export). -/
theorem singleCoordinate_1d (b : Bad (nativePlaceSelection T)) (R : Real) (hR : 0 < R) :
    rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
        (R / (qVFamTensorP T b : Real))) <
      rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b) R) :=
  strictChain_1d T b R hR

/-- Product strict Haar increase (re-export). -/
theorem singleCoordinate_product :
    rootExtensionProductHaar T (rpRegion T) <
      rootExtensionProductHaar T (s1902Hull T) :=
  strictChain_product T

/-- `strict_measure` as a THEOREM (re-export). -/
theorem singleCoordinate_strict_measure :
    rpVolume T (rpRegion T) < rpVolume T (s1902Hull T) :=
  strictChain_strict_measure T

def singleCoordinateRows : List (String × String × String) :=
  [ ("1D strict ball measure", "singleCoordinate_1d", "GREEN (via strictChain_1d)"),
    ("product strict Haar increase", "singleCoordinate_product", "GREEN (via strictChain_product)"),
    ("strict_measure theorem", "singleCoordinate_strict_measure", "GREEN (via strictChain_strict_measure)"),
    ("scope", "thin re-export; no canonical change", "INTEGRITY") ]

theorem singleCoordinateRows_length : singleCoordinateRows.length = 4 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1HaarSingleCoordinateStrictActual.singleCoordinate_strict_measure

end LeanFormal.IUT.XiFPaper.Mzk1HaarSingleCoordinateStrictActual

end