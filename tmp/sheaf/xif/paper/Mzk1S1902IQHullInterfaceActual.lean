/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HaarStrictScalingProductActual
import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction
import Mathlib.Tactic

/-! # A614 hull: concrete instantiation of `IQHullLogVolumeInterface` on S1902

The bridge interface field `hullData : IQHullLogVolumeInterface` was abstract.
This module instantiates it on the real S1902 carrier:

* `imageSet = {qPilotInThetaCarrier T}` (the q-pilot image union);
* `hull = s1902Hull T` (the actual product region);
* `logVolume = rootExtensionProductHaar T` (the actual Haar measure);
* `unitRegion = s1902Hull T`, `scaleShift = id` (normalization by the actual
  compact hull; the scaling is trivial for this carrier);
* containment from `qPilotInThetaCarrier_mem_hull`; finiteness from the green
  product file (`hullRegion_measure_lt_top`).

All fields are PROVED; no named field remains and no sorry/axiom. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1S1902IQHullInterfaceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictScalingProductActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- The image union is contained in the actual hull. -/
theorem s1902ImageSet_subset_hull :
    ({qPilotInThetaCarrier T} : Set (S1902Carrier T)) ⊆ s1902Hull T := by
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  exact qPilotInThetaCarrier_mem_hull T

/-- The actual s1902 hull has finite product Haar measure (re-export). -/
theorem s1902Hull_measure_lt_top :
    rootExtensionProductHaar T (s1902Hull T) < ⊤ := by
  simpa [hullRegion_eq_s1902Hull] using hullRegion_measure_lt_top (T := T)

/-- **Concrete `IQHullLogVolumeInterface` on the real S1902 carrier.** -/
noncomputable def s1902IQHullInterface :
    LeanFormal.IUT.IQHullLogVolumeInterface (S1902Carrier T) where
  imageSet := {qPilotInThetaCarrier T}
  hull := s1902Hull T
  imageSet_subset_hull := s1902ImageSet_subset_hull T
  logVolume := rootExtensionProductHaar T
  logVolume_mono := fun hST => measure_mono hST
  unitRegion := s1902Hull T
  scaleShift := id
  hull_subset_scaleShift := by
    intro x hx
    exact ⟨x, hx, rfl⟩
  unitRegion_logVolume_lt_top := s1902Hull_measure_lt_top T
  scaleShift_unitRegion_logVolume_le := by
    simp

/-- Paper-level finiteness conclusion for the concrete interface. -/
theorem s1902IQHull_hull_logVolume_lt_top :
    (s1902IQHullInterface T).logVolume (s1902IQHullInterface T).hull < ⊤ :=
  (s1902IQHullInterface T).hull_logVolume_lt_top

/-- The normalized lower bound propagates from the image union to the hull. -/
theorem s1902IQHull_imageSet_logVolume_le_hull :
    (s1902IQHullInterface T).logVolume (s1902IQHullInterface T).imageSet ≤
      (s1902IQHullInterface T).logVolume (s1902IQHullInterface T).hull :=
  (s1902IQHullInterface T).imageSet_logVolume_le_hull

def s1902IQHullRows : List (String × String × String) :=
  [ ("imageSet_subset_hull", "qPilotInThetaCarrier_mem_hull", "PROVED"),
    ("logVolume_mono", "measure_mono", "PROVED"),
    ("unitRegion finiteness", "hullRegion_measure_lt_top", "PROVED (product file)"),
    ("hull_subset_scaleShift", "id image", "PROVED"),
    ("scaleShift_unitRegion_logVolume_le", "id image", "PROVED"),
    ("scope", "real S1902 carrier instantiation; no ABC closure", "INTEGRITY") ]

theorem s1902IQHullRows_length : s1902IQHullRows.length = 6 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1S1902IQHullInterfaceActual.s1902IQHull_hull_logVolume_lt_top
#print axioms LeanFormal.IUT.XiFPaper.Mzk1S1902IQHullInterfaceActual.s1902IQHull_imageSet_logVolume_le_hull

end LeanFormal.IUT.XiFPaper.Mzk1S1902IQHullInterfaceActual

end