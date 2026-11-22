import tmp.sheaf.xif.paper.S2570AEvalChainActual
import tmp.sheaf.xif.paper.S2555Mod613BezoutActual
noncomputable section
open Polynomial
set_option maxRecDepth 2000000
namespace P
open LeanFormal.IUT.XiFPaper.S2570AEvalChainActual
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
example : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 12) - X := G_dvd_pow_sub_X
end P
end
