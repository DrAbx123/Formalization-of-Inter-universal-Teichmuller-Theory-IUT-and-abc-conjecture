import tmp.sheaf.xif.paper.S2570Chain6to9Actual
import tmp.sheaf.xif.paper.S2565ChainComp3Actual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2570Chain10to12Actual

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2569GdivActual

lemma pow_eq_10 : (X : (ZMod 613)[X]) ^ (613 ^ 10) = ((X : (ZMod 613)[X]) ^ (613 ^ 9)) ^ 613 := by
  rw [← pow_mul]
  congr 1

lemma chain10_dvd : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 10) - T10 := by
  rw [pow_eq_10]
  exact LeanFormal.IUT.XiFPaper.S2570ChainStepActual.chain_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 9)) (Q := T9) (R := T10)
    LeanFormal.IUT.XiFPaper.S2570Chain6to9Actual.chain9_dvd LeanFormal.IUT.XiFPaper.S2565ChainComp3Actual.chain_dvd_9

lemma pow_eq_11 : (X : (ZMod 613)[X]) ^ (613 ^ 11) = ((X : (ZMod 613)[X]) ^ (613 ^ 10)) ^ 613 := by
  rw [← pow_mul]
  congr 1

lemma chain11_dvd : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 11) - T11 := by
  rw [pow_eq_11]
  exact LeanFormal.IUT.XiFPaper.S2570ChainStepActual.chain_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 10)) (Q := T10) (R := T11)
    LeanFormal.IUT.XiFPaper.S2570Chain10to12Actual.chain10_dvd LeanFormal.IUT.XiFPaper.S2565ChainComp3Actual.chain_dvd_10

lemma pow_eq_12 : (X : (ZMod 613)[X]) ^ (613 ^ 12) = ((X : (ZMod 613)[X]) ^ (613 ^ 11)) ^ 613 := by
  rw [← pow_mul]
  congr 1

lemma chain12_dvd : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 12) - T12 := by
  rw [pow_eq_12]
  exact LeanFormal.IUT.XiFPaper.S2570ChainStepActual.chain_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 11)) (Q := T11) (R := T12)
    LeanFormal.IUT.XiFPaper.S2570Chain10to12Actual.chain11_dvd LeanFormal.IUT.XiFPaper.S2565ChainComp3Actual.chain_dvd_11

end LeanFormal.IUT.XiFPaper.S2570Chain10to12Actual
end
