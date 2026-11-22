import tmp.sheaf.xif.paper.S2570ChainStepActual
import tmp.sheaf.xif.paper.S2566ChainComp1aActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2570Chain2Actual

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2569GdivActual

lemma pow_eq_2 : (X : (ZMod 613)[X]) ^ (613 ^ 2) = ((X : (ZMod 613)[X]) ^ (613 ^ 1)) ^ 613 := by
  rw [← pow_mul]
  congr 1

lemma chain2_dvd : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 2) - T2 := by
  rw [pow_eq_2]
  exact LeanFormal.IUT.XiFPaper.S2570ChainStepActual.chain_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 1)) (Q := T1) (R := T2)
    LeanFormal.IUT.XiFPaper.S2564Chain1IdentityActual.chain1_dvd LeanFormal.IUT.XiFPaper.S2566ChainComp1aActual.chain_dvd_1

end LeanFormal.IUT.XiFPaper.S2570Chain2Actual
end