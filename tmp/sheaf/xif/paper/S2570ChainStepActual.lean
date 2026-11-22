import tmp.sheaf.xif.paper.S2569GdivActual
import tmp.sheaf.xif.paper.S2564Chain1IdentityActual


noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2570ChainStepActual

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2569GdivActual
instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

lemma chain_step {P Q R : (ZMod 613)[X]}
    (h1 : G ∣ P - Q) (h2 : G ∣ Q.comp T1 - R) :
    G ∣ P ^ 613 - R := by
  have hp : G ∣ P ^ 613 - Q ^ 613 := h1.trans (sub_dvd_pow_sub_pow P Q 613)
  have hq : G ∣ Q ^ 613 - Q.comp T1 := G_dvd_pow_sub_comp Q
  have hsum : G ∣ P ^ 613 - Q.comp T1 := by
    have h := dvd_add hp hq
    convert h using 1 <;> ring
  have h := dvd_add hsum h2
  convert h using 1 <;> ring

end LeanFormal.IUT.XiFPaper.S2570ChainStepActual
end
