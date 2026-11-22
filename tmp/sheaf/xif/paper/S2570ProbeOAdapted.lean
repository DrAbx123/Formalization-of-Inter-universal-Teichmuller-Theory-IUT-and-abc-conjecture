import tmp.sheaf.xif.paper.S2570AEvalChainActual
import tmp.sheaf.xif.paper.S2555Mod613BezoutActual
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 500000
open Polynomial
namespace PO
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2570AEvalChainActual
example (q : (ZMod 613)[X]) (hq : (X : (ZMod 613)[X]) ^ (613 ^ 4) - T4 = G * q) :
    (X : (ZMod 613)[X]) ^ (613 ^ 4) - X = (T4 - X) + q * G := by
  linear_combination hq
end PO
end
