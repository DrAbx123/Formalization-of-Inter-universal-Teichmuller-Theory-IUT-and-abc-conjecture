import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial
namespace Probe2565

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual

example : (C (2 : ZMod 613) * X + C 3) * (C (5 : ZMod 613) * X + C 7) =
    C (10 : ZMod 613) * X ^ 2 + C (29 : ZMod 613) * X + C 21 := by
  ring_nf

example : (C (2 : ZMod 613) * X + C 3) * (C (5 : ZMod 613) * X + C 7) =
    C (10 : ZMod 613) * X ^ 2 + C (29 : ZMod 613) * X + C 21 := by
  simp only [Polynomial.C_eq_natCast]
  ring_nf

example : (C (2 : ZMod 613) * X + C 3).comp (C (5 : ZMod 613) + X) =
    C (13 : ZMod 613) + C 2 * X := by
  simp
  ring_nf

end Probe2565
