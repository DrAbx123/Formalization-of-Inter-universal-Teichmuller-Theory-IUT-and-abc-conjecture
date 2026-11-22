import tmp.sheaf.xif.paper.S2570AEvalChainActual
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 500000
open Polynomial
namespace PL
def E4 : ℕ := 613 ^ 4
example (b : (ZMod 613)[X]) : ((X : (ZMod 613)[X]) ^ E4 - X) - (b - X) = (X : (ZMod 613)[X]) ^ E4 - b :=
  sub_sub_sub_cancel_right _ _ _
end PL
end
