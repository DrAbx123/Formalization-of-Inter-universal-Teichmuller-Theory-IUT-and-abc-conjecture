import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardAMPLThetaBoundSupply

/-! # S3131 instantiation attempt: hull finiteness from CardAMPL supply -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3131CardAMPLHullFinitenessActual

universe u

/-- REUSE: the CardAMPL supply makes the hull log-volume finite (not top). -/
theorem hull_logVolume_ne_top_of_supply {X : Type u} {W : IQHullLogVolumeInterface X}
    (S : CardAMPLThetaBoundSupply W) : W.logVolume W.hull ≠ ⊤ := by
  rw [iqHull_logVolume_hull_eq_ofReal W]
  exact ENNReal.ofReal_lt_top.ne

/-- Consequently the hull real volume is at most the supply constant. -/
theorem hull_realVolume_le_supply {X : Type u} {W : IQHullLogVolumeInterface X}
    (S : CardAMPLThetaBoundSupply W) : iqHullRealVolume W ≤ S.theta :=
  CardAMPLThetaBoundSupply.realVolume_le S

#check hull_logVolume_ne_top_of_supply

end LeanFormal.IUT.XiFPaper.S3131CardAMPLHullFinitenessActual
end