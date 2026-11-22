import tmp.sheaf.xif.paper.S2570AEvalChainActual
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 500000
open Polynomial
namespace PK
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
def E4 : ℕ := 613 ^ 4
example : ((X : (ZMod 613)[X]) ^ E4 - X) - (T4 - X) = (X : (ZMod 613)[X]) ^ E4 - T4 :=
  sub_sub_sub_cancel_right (G := (ZMod 613)[X]) _ _ _
end PK
end
