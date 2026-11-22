import tmp.sheaf.xif.paper.S2570ChainStepActual
import tmp.sheaf.xif.paper.S2570Chain2Actual
import tmp.sheaf.xif.paper.S2566ChainComp1bActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 500000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2570Chain3Actual

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2569GdivActual

lemma pow_eq_3 : (X : (ZMod 613)[X]) ^ (613 ^ 3) = ((X : (ZMod 613)[X]) ^ (613 ^ 2)) ^ 613 := by
  rw [← pow_mul]
  congr 1

lemma chain3_dvd : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 3) - T3 := by
  rw [pow_eq_3]
  let P : (ZMod 613)[X] := (X : (ZMod 613)[X]) ^ (613 ^ 2)
  have hP : P = (X : (ZMod 613)[X]) ^ (613 ^ 2) := rfl
  have h1 : G ∣ P - T2 := by
    rw [hP]
    exact LeanFormal.IUT.XiFPaper.S2570Chain2Actual.chain2_dvd
  have h2 : G ∣ T2.comp T1 - T3 := LeanFormal.IUT.XiFPaper.S2566ChainComp1bActual.chain_dvd_2
  have hstep : G ∣ P ^ 613 - T3 := LeanFormal.IUT.XiFPaper.S2570ChainStepActual.chain_step (P := P) (Q := T2) (R := T3) h1 h2
  change G ∣ P ^ 613 - T3
  exact hstep

end LeanFormal.IUT.XiFPaper.S2570Chain3Actual
end