import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction

/-! Mainline: chain of hull log-volume finiteness with the EReal-to-real dictionary
  (new iff/consumer composed from the tree finiteness theorem). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullVolumeFiniteChainActual

open LeanFormal.IUT

theorem hull_logVolume_lt_top_iff_exists_real {X : Type*}
    (W : IQHullLogVolumeInterface X) :
    W.logVolume W.hull < ⊤ ↔ ∃ θ : ℝ, W.logVolume W.hull = θ := by
  rw [lt_top_iff_ne_top, EReal.ne_top_iff_exists]

theorem hull_logVolume_exists_real_of_lt_top {X : Type*}
    (W : IQHullLogVolumeInterface X) (h : W.logVolume W.hull < ⊤) :
    ∃ θ : ℝ, W.logVolume W.hull = θ :=
  (hull_logVolume_lt_top_iff_exists_real W).mp h

end LeanFormal.IUT.XiFPaper.Mzk1HullVolumeFiniteChainActual