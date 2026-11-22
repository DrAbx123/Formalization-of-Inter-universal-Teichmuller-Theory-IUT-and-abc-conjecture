import tmp.sheaf.xif.paper.S2570Chain5Actual
import tmp.sheaf.xif.paper.S2565ChainComp2Actual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2570Chain6to9Actual

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2569GdivActual

lemma pow_eq_6 : (X : (ZMod 613)[X]) ^ (613 ^ 6) = ((X : (ZMod 613)[X]) ^ (613 ^ 5)) ^ 613 := by
  rw [← pow_mul]
  congr 1

lemma chain6_dvd : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 6) - T6 := by
  rw [pow_eq_6]
  exact LeanFormal.IUT.XiFPaper.S2570ChainStepActual.chain_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 5)) (Q := T5) (R := T6)
    LeanFormal.IUT.XiFPaper.S2570Chain5Actual.chain5_dvd LeanFormal.IUT.XiFPaper.S2565ChainComp2Actual.chain_dvd_5

lemma pow_eq_7 : (X : (ZMod 613)[X]) ^ (613 ^ 7) = ((X : (ZMod 613)[X]) ^ (613 ^ 6)) ^ 613 := by
  rw [← pow_mul]
  congr 1

lemma chain7_dvd : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 7) - T7 := by
  rw [pow_eq_7]
  exact LeanFormal.IUT.XiFPaper.S2570ChainStepActual.chain_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 6)) (Q := T6) (R := T7)
    LeanFormal.IUT.XiFPaper.S2570Chain6to9Actual.chain6_dvd LeanFormal.IUT.XiFPaper.S2565ChainComp2Actual.chain_dvd_6

lemma pow_eq_8 : (X : (ZMod 613)[X]) ^ (613 ^ 8) = ((X : (ZMod 613)[X]) ^ (613 ^ 7)) ^ 613 := by
  rw [← pow_mul]
  congr 1

lemma chain8_dvd : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 8) - T8 := by
  rw [pow_eq_8]
  exact LeanFormal.IUT.XiFPaper.S2570ChainStepActual.chain_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 7)) (Q := T7) (R := T8)
    LeanFormal.IUT.XiFPaper.S2570Chain6to9Actual.chain7_dvd LeanFormal.IUT.XiFPaper.S2565ChainComp2Actual.chain_dvd_7

lemma pow_eq_9 : (X : (ZMod 613)[X]) ^ (613 ^ 9) = ((X : (ZMod 613)[X]) ^ (613 ^ 8)) ^ 613 := by
  rw [← pow_mul]
  congr 1

lemma chain9_dvd : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 9) - T9 := by
  rw [pow_eq_9]
  exact LeanFormal.IUT.XiFPaper.S2570ChainStepActual.chain_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 8)) (Q := T8) (R := T9)
    LeanFormal.IUT.XiFPaper.S2570Chain6to9Actual.chain8_dvd LeanFormal.IUT.XiFPaper.S2565ChainComp2Actual.chain_dvd_8

end LeanFormal.IUT.XiFPaper.S2570Chain6to9Actual
end
