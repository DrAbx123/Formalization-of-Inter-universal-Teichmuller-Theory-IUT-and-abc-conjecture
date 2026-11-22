import tmp.sheaf.xif.paper.S2009DicksonActual

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open LeanFormal.IUT.XiFPaper.S2009DicksonActual

namespace LeanFormal.IUT.XiFPaper.S2615DetTwelveCycleActual

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem S2615_det_cycle12 (h : GL2)
    (hc : (pairPermHom h).cycleType = ({12} : Multiset ℕ)) :
    (Matrix.GeneralLinearGroup.det h : K5) = 2 ∨
      (Matrix.GeneralLinearGroup.det h : K5) = 3 := by
  revert h
  decide

end LeanFormal.IUT.XiFPaper.S2615DetTwelveCycleActual
end