import tmp.sheaf.xif.paper.S2570Chain4ActualAdapted
import tmp.sheaf.xif.paper.S2566ChainComp1dActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2570Chain5ActualAdapted

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2569GdivActual

lemma pow_eq_5 : (X : (ZMod 613)[X]) ^ (613 ^ 5) = ((X : (ZMod 613)[X]) ^ (613 ^ 4)) ^ 613 := by
  rw [← pow_mul]

lemma chain5_dvd : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 5) - T5 := by
  rw [pow_eq_5]
  have h1 : G ∣ ((X : (ZMod 613)[X]) ^ (613 ^ 4)) ^ 613 - (T4) ^ 613 := LeanFormal.IUT.XiFPaper.S2570Chain4ActualAdapted.chain4_dvd.trans (sub_dvd_pow_sub_pow ((X : (ZMod 613)[X]) ^ (613 ^ 4)) (T4) 613)
  have h2 : G ∣ (T4) ^ 613 - (T4).comp T1 := G_dvd_pow_sub_comp (T4)
  have h3 : G ∣ (T4).comp T1 - T5 := LeanFormal.IUT.XiFPaper.S2566ChainComp1dActual.chain_dvd_4
  have h := dvd_add (dvd_add h1 h2) h3
  convert h using 1 <;> ring

end LeanFormal.IUT.XiFPaper.S2570Chain5ActualAdapted
end
