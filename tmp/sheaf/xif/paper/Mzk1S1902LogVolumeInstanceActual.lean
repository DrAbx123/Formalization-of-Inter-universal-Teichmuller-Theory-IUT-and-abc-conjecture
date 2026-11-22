/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.PaperRootExtensionNormBoundActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.S664RootQUnitNormLeOneActual
import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import Mathlib.Tactic

/-! # A549: attempt to eliminate `strict_measure` via the S1902 real log-volume

`s1902LogVolume` (S1902ActualThetaHullActual) is the actual normalized Haar
log-volume on the Theta-pilot carrier; it is monotone under inclusion
(`s1902LogVolume_mono`).  This file defines its real-valued version
`s1902VolReal S = (s1902LogVolume T S).toReal` and proves:

* `s1902VolReal_mono_of_finite`: monotonicity on sets whose upper set has finite
  log-volume (the raw ENNReal `toReal` is not monotone at `⊤`; finiteness is
  needed);
* `s1902VolReal_unitRegion = 1`, hence positive;
* `s1902VolReal_hull_le_one`: the actual hull is inside the unit region
  (RootQUnitNormLeOne), so its log-volume is at most 1;
* `s1902VolReal_hull_lt_top` / finiteness of the hull volume;
* `s1902VolReal_qImage_le_hull`: the singletons are contained in the hull, giving
  the non-strict comparison.

AUDIT (why `strict_measure` cannot be eliminated with singleton q-region):
the current `KummerXiERealization` uses `qRegion = {qPilotInThetaCarrier}`, a
singleton, which has Haar log-volume `0`; hence `q_pos` fails and the strict
inequality `0 < vol hull` is not the paper inequality.  The paper q-pilot image is
a positive-measure log-shell region, not a point.  Therefore eliminating the named
`strict_measure` requires (i) a positive-measure q-pilot region (e.g. a product
ball around the transported q image) and (ii) the proof that the hull contains it
with strictly larger Haar volume.  We do not claim that here; the named field stays
minimal and explicit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1S1902LogVolumeInstanceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionNormBoundActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.S664RootQUnitNormLeOneActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open scoped ENNReal BigOperators Pointwise

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The real-valued version of the actual S1902 normalized Haar log-volume. -/
noncomputable def s1902VolReal : Set (S1902Carrier T) -> Real :=
  fun S => (s1902LogVolume T S).toReal

theorem s1902VolReal_def (S : Set (S1902Carrier T)) :
    s1902VolReal T S = (s1902LogVolume T S).toReal := rfl

/-- Monotonicity of the real log-volume on sets with finite upper log-volume. -/
theorem s1902VolReal_mono_of_finite {S U : Set (S1902Carrier T)} (hSU : S <= U)
    (hU : s1902LogVolume T U < ⊤) :
    s1902VolReal T S <= s1902VolReal T U := by
  unfold s1902VolReal
  exact ENNReal.toReal_mono (ne_of_lt hU) (s1902LogVolume_mono T hSU)

/-- The unit region has real log-volume 1. -/
theorem s1902VolReal_unitRegion : s1902VolReal T (s1902UnitRegion T) = 1 := by
  unfold s1902VolReal
  rw [show s1902LogVolume T (s1902UnitRegion T) = (1 : ENNReal) from s1902LogVolume_unitRegion T]
  norm_num

theorem s1902VolReal_unitRegion_pos : 0 < s1902VolReal T (s1902UnitRegion T) := by
  rw [s1902VolReal_unitRegion]
  norm_num

/-- The actual Theta hull lies in the unit region, hence its log-volume is at most 1. -/
theorem s1902VolReal_hull_le_one : s1902VolReal T (s1902Hull T) <= 1 := by
  have hsub : s1902Hull T <= s1902UnitRegion T := by
    change rootExtensionProductImageHull T <=
      LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual.rootExtensionProductUnitBall T
    exact rootExtensionProductImageHull_subset_unitBall (T := T) (rootQUnitNormLeOne (T := T))
  have hmono := s1902LogVolume_mono T hsub
  have hunit : s1902LogVolume T (s1902UnitRegion T) = 1 := s1902LogVolume_unitRegion T
  have hfin : s1902LogVolume T (s1902UnitRegion T) < ⊤ := by
    rw [hunit]
    norm_num
  have hle := ENNReal.toReal_mono (ne_of_lt hfin) hmono
  rwa [hunit, ENNReal.toReal_one] at hle

/-- The hull log-volume is finite. -/
theorem s1902VolReal_hull_lt_top : s1902LogVolume T (s1902Hull T) < ⊤ :=
  s1902Hull_logVolume_lt_top T

/-- The q-pilot image (singleton) is contained in the hull, giving the non-strict
real log-volume comparison. -/
theorem s1902VolReal_qImage_le_hull :
    s1902VolReal T {qPilotInThetaCarrier T} <= s1902VolReal T (s1902Hull T) := by
  apply s1902VolReal_mono_of_finite
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact qPilotInThetaCarrier_mem_hull T
  · exact s1902VolReal_hull_lt_top T

/-- Partial data record: everything provable for the S1902 real log-volume.  The
`q_pos`/`strict_measure` fields are deliberately absent (see the audit). -/
structure S1902LogVolumeInstance where
  vol : Set (S1902Carrier T) -> Real
  vol_def : forall S, vol S = (s1902LogVolume T S).toReal
  mono_finite : forall {S U : Set (S1902Carrier T)}, S <= U ->
    s1902LogVolume T U < ⊤ -> vol S <= vol U
  unitRegion_eq_one : vol (s1902UnitRegion T) = 1
  hull_le_one : vol (s1902Hull T) <= 1
  hull_lt_top : s1902LogVolume T (s1902Hull T) < ⊤

noncomputable def s1902LogVolumeInstance : S1902LogVolumeInstance T where
  vol := s1902VolReal T
  vol_def := fun S => s1902VolReal_def T S
  mono_finite := fun hSU hU => s1902VolReal_mono_of_finite T hSU hU
  unitRegion_eq_one := s1902VolReal_unitRegion T
  hull_le_one := s1902VolReal_hull_le_one T
  hull_lt_top := s1902VolReal_hull_lt_top T

end LeanFormal.IUT.XiFPaper.Mzk1S1902LogVolumeInstanceActual

end
