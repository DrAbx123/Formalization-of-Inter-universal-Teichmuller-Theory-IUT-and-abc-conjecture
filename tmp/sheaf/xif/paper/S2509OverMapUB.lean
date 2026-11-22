import tmp.sheaf.xif.paper.S2508CuspDataUB

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2508CuspDataUB
open LeanFormal.IUT.XiFPaper.S2504UnifiedBaseActual
open LeanFormal.IUT.XiFPaper.S2505AwayEquivActual
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S2509OverMapUB

/-- The actual over-map for the X1-chart `Spec UB[x] -> P1_UB`. -/
noncomputable def S2509OverMap : S2504FOver' ⟶ S2504P1Over :=
  S2508ChartOverMap

theorem S2509OverMap_left :
    Over.left S2509OverMap = S2504ToP1 := rfl

#print axioms S2509OverMap
end LeanFormal.IUT.XiFPaper.S2509OverMapUB
end