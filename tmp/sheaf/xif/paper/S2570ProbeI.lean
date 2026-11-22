import tmp.sheaf.xif.paper.S2570AEvalChainActual
import tmp.sheaf.xif.paper.S2555Mod613BezoutActual
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 500000
open Polynomial
namespace PI
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2570AEvalChainActual
example : G ∣ ((X : (ZMod 613)[X]) ^ (613 ^ 4) - X) - (T4 - X) := by
  rw [show ((X : (ZMod 613)[X]) ^ (613 ^ 4) - X) - (T4 - X) =
      (X : (ZMod 613)[X]) ^ (613 ^ 4) - T4 from
    sub_sub_sub_cancel_right _ _ _]
  exact LeanFormal.IUT.XiFPaper.S2570AEvalChainActual.G_dvd_pow4_sub_T4
end PI
end
