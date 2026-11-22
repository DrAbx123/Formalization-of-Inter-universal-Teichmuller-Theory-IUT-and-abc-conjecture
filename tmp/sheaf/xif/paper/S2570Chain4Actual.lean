import tmp.sheaf.xif.paper.S2570Chain3Actual
import tmp.sheaf.xif.paper.S2566ChainComp1cActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2570Chain4Actual

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2569GdivActual

lemma pow_eq_4 : (X : (ZMod 613)[X]) ^ (613 ^ 4) = ((X : (ZMod 613)[X]) ^ (613 ^ 3)) ^ 613 := by
  rw [← pow_mul]

lemma chain4_dvd : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 4) - T4 := by
  rw [pow_eq_4]
  have h1 : G ∣ ((X : (ZMod 613)[X]) ^ (613 ^ 3)) ^ 613 - (T3) ^ 613 := LeanFormal.IUT.XiFPaper.S2570Chain3Actual.chain3_dvd.trans (sub_dvd_pow_sub_pow ((X : (ZMod 613)[X]) ^ (613 ^ 3)) (T3) 613)
  have h2 : G ∣ (T3) ^ 613 - (T3).comp T1 := G_dvd_pow_sub_comp (T3)
  have h3 : G ∣ (T3).comp T1 - T4 := LeanFormal.IUT.XiFPaper.S2566ChainComp1cActual.chain_dvd_3
  have h := dvd_add (dvd_add h1 h2) h3
  convert h using 1 <;> ring

end LeanFormal.IUT.XiFPaper.S2570Chain4Actual
end
