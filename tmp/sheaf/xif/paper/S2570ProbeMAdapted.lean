import tmp.sheaf.xif.paper.S2570AEvalChainActual
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 500000
open Polynomial
namespace PM
def E4 : ℕ := 613 ^ 4
example : (X : (ZMod 613)[X]) ^ E4 = (X : (ZMod 613)[X]) ^ E4 := rfl
end PM
end
