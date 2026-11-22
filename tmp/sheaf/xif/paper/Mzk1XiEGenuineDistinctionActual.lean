/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import Mathlib.Tactic

/-!
# Mzk1XiEGenuineDistinctionActual — trivial q_in_possible vs genuine possible_in_hull

A537: in the xi-e containment requirement the field `q_in_possible` is a
reflexive/definitional inclusion (the q-pilot image is one of the possible images
by construction), while `possible_in_hull` is the genuine mathematical content:
the possible image lies in the actual Theta hull, proved from the SHE root relation,
the norm bound and the hull radius.  The hull contains `0` but the q image does not,
so the inclusion is strict and cannot be a definitional identification.

No new axiom; no True placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1XiEGenuineDistinctionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The trivial part of xi-e: reflexivity of the possible-image set with itself
(no mathematical content). -/
theorem q_in_possible_trivial :
    {qPilotInThetaCarrier T} ⊆ ({qPilotInThetaCarrier T} : Set (S1902Carrier T)) :=
  subset_rfl

/-- The genuine part of xi-e: the (singleton) possible image lies in the actual
Theta hull, from `qPilotInThetaCarrier_mem_hull`. -/
theorem possible_in_hull_genuine :
    ({qPilotInThetaCarrier T} : Set (S1902Carrier T)) ⊆ s1902Hull T := by
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  exact qPilotInThetaCarrier_mem_hull T

/-- The hull contains `0` (every factor closed ball is centered at zero). -/
theorem zero_mem_s1902Hull : (0 : S1902Carrier T) ∈ s1902Hull T := by
  rw [s1902Hull, rootExtensionProductImageHull, Set.mem_pi]
  intro b _
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_zero]
  exact_mod_cast (rootImageRadius_pos T b).le

/-- The q-pilot image is nonzero at each bad place (the q candidate is nonzero). -/
theorem qPilotInThetaCarrier_apply_ne_zero
    (b : Bad (nativePlaceSelection T)) :
    qPilotInThetaCarrier T b ≠ 0 := by
  have hx : ((qVFamily T b).q : rootBase T b) ≠ 0 := (qVFamily T b).q_ne_zero
  have hmap : algebraMap (rootBase T b) (rootNormedExtension T b)
      ((qVFamily T b).q : rootBase T b) ≠ 0 := by
    have hinj := (algebraMap (rootBase T b) (rootNormedExtension T b)).injective.ne hx
    simpa using hinj
  simpa [qPilotInThetaCarrier, qPilotCompletionImage, completionToRootExtension] using hmap

/-- The q-pilot image is nonzero wherever a bad place exists. -/
theorem qPilotInThetaCarrier_ne_zero : qPilotInThetaCarrier T ≠ 0 := by
  intro h
  have b : Bad (nativePlaceSelection T) := Classical.choice (bad_nonempty T)
  exact qPilotInThetaCarrier_apply_ne_zero T b (by rw [h])

/-- The genuine hull inclusion is **strict**: the hull contains `0`, the singleton
does not, so it cannot be a definitional equality `hull := qRegion`. -/
theorem possible_in_hull_strict :
    ({qPilotInThetaCarrier T} : Set (S1902Carrier T)) ≠ s1902Hull T := by
  intro h
  have h0 : (0 : S1902Carrier T) ∈ ({qPilotInThetaCarrier T} : Set (S1902Carrier T)) := by
    rw [h]
    exact zero_mem_s1902Hull T
  rw [Set.mem_singleton_iff] at h0
  exact qPilotInThetaCarrier_ne_zero T h0.symm

#check possible_in_hull_genuine
#check possible_in_hull_strict

end LeanFormal.IUT.XiFPaper.Mzk1XiEGenuineDistinctionActual
end
