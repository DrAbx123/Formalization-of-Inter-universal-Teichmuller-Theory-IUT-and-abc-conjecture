/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ExactHullVMainTermActual
import Mathlib.Tactic
/-! # GAP-P6-C17-THETA-S3137 layer 2: normalized log hull -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaVLayerNormalizedActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ExactHullVMainTermActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
theorem normalizedLayer_nonpos :
    rootExtensionProductNormalizedLog T (s1902Hull T) ≤ 0 :=
  normalizedLog_hull_nonpos T
def rows : List String := ["rootExtensionProductNormalizedLog", "s1902Hull", "≤ 0"]
theorem rows_length : rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1ThetaVLayerNormalizedActual
end