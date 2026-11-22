/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ScaledPaper312Actual
import tmp.sheaf.xif.paper.Mzk1HaarProductStrictMainlineActual
import Mathlib.Tactic
/-! # GAP-P7-HULL-UB: paper normalized V = normalizedLog hull (k=0 identity) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1HullUBPaperVIdentityActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1ScaledPaper312Actual
open LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullShaActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarProductStrictMainlineActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

instance badNonempty : Nonempty (Bad (nativePlaceSelection T)) := by
  rcases (nativePlaceSelection T).V_mod_bad_nonempty with ⟨p, hp⟩
  exact ⟨⟨p, hp⟩⟩
theorem paperV_zero_eq_normalizedLog :
    thetaScaledLog T 0 = rootExtensionProductNormalizedLog T (s1902Hull T) := by
  unfold thetaScaledLog paperThetaHullScaled
  rw [Mzk1ScaledThetaHullShaActual.scaledThetaHull_zero,
    Mzk1HaarProductStrictMainlineActual.fullRegion_eq_hull]
theorem paperV_zero_eq_fullRegion_normalizedLog :
    thetaScaledLog T 0 = rootExtensionProductNormalizedLog T (fullRegion T) := by
  unfold thetaScaledLog paperThetaHullScaled
  rw [Mzk1ScaledThetaHullShaActual.scaledThetaHull_zero]
def rows : List String := ["thetaScaledLog 0 = normalizedLog fullRegion", "fullRegion = s1902Hull (rfl)", "paper V identity"]
theorem rows_length : rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1HullUBPaperVIdentityActual
end