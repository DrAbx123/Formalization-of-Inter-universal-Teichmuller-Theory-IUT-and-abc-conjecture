import tmp.sheaf.xif.paper.S2553Mod613DegreeActual
import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual
import tmp.sheaf.xif.paper.S2555Mod613BezoutActual
import tmp.sheaf.xif.paper.S2564Chain1IdentityActual
import tmp.sheaf.xif.paper.S2566ChainComp1aActual
import tmp.sheaf.xif.paper.S2566ChainComp1bActual
import tmp.sheaf.xif.paper.S2566ChainComp1cActual
import tmp.sheaf.xif.paper.S2566ChainComp1dActual
import tmp.sheaf.xif.paper.S2565ChainComp2Actual
import tmp.sheaf.xif.paper.S2565ChainComp3Actual
import tmp.sheaf.xif.paper.S2569GdivActual
import tmp.sheaf.xif.paper.S2550RabinCriterionActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2570F613IrreducibleActual

open LeanFormal.IUT.XiFPaper.S2553Mod613DegreeActual
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2569GdivActual

instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

lemma G_monic : G.Monic := by unfold G; monicity!
lemma G_natDegree : G.natDegree = 12 := by unfold G; compute_degree!

lemma chain_step {P Q R : (ZMod 613)[X]}
    (h1 : G ∣ P - Q) (h2 : G ∣ Q.comp T1 - R) :
    G ∣ P ^ 613 - R := by
  have hp : G ∣ P ^ 613 - Q ^ 613 := h1.trans (sub_dvd_pow_sub_pow P Q 613)
  have hq : G ∣ Q ^ 613 - Q.comp T1 := G_dvd_pow_sub_comp Q
  have hsum : G ∣ P ^ 613 - Q.comp T1 := by
    have := dvd_add hp hq
    convert this using 1 <;> ring
  have := dvd_add hsum h2
  convert this using 1 <;> ring

lemma chain2_dvd : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 2) - T2 := by
  have h := chain_step (P := (X : (ZMod 613)[X])) (Q := T1) (R := T2)
    LeanFormal.IUT.XiFPaper.S2564Chain1IdentityActual.chain1_dvd
    LeanFormal.IUT.XiFPaper.S2566ChainComp1aActual.chain_dvd_1
  convert h using 1
  rw [← pow_mul]; norm_num

lemma chain3_dvd : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 3) - T3 := by
  have h := chain_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 2)) (Q := T2) (R := T3)
    chain2_dvd LeanFormal.IUT.XiFPaper.S2566ChainComp1bActual.chain_dvd_2
  convert h using 1
  rw [← pow_mul]; norm_num

lemma chain4_dvd : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 4) - T4 := by
  have h := chain_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 3)) (Q := T3) (R := T4)
    chain3_dvd LeanFormal.IUT.XiFPaper.S2566ChainComp1cActual.chain_dvd_3
  convert h using 1
  rw [← pow_mul]; norm_num

lemma chain5_dvd : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 5) - T5 := by
  have h := chain_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 4)) (Q := T4) (R := T5)
    chain4_dvd LeanFormal.IUT.XiFPaper.S2566ChainComp1dActual.chain_dvd_4
  convert h using 1
  rw [← pow_mul]; norm_num

lemma chain6_dvd : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 6) - T6 := by
  have h := chain_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 5)) (Q := T5) (R := T6)
    chain5_dvd LeanFormal.IUT.XiFPaper.S2565ChainComp2Actual.chain_dvd_5
  convert h using 1
  rw [← pow_mul]; norm_num

lemma chain7_dvd : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 7) - T7 := by
  have h := chain_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 6)) (Q := T6) (R := T7)
    chain6_dvd LeanFormal.IUT.XiFPaper.S2565ChainComp2Actual.chain_dvd_6
  convert h using 1
  rw [← pow_mul]; norm_num

lemma chain8_dvd : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 8) - T8 := by
  have h := chain_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 7)) (Q := T7) (R := T8)
    chain7_dvd LeanFormal.IUT.XiFPaper.S2565ChainComp2Actual.chain_dvd_7
  convert h using 1
  rw [← pow_mul]; norm_num

lemma chain9_dvd : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 9) - T9 := by
  have h := chain_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 8)) (Q := T8) (R := T9)
    chain8_dvd LeanFormal.IUT.XiFPaper.S2565ChainComp2Actual.chain_dvd_8
  convert h using 1
  rw [← pow_mul]; norm_num

lemma chain10_dvd : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 10) - T10 := by
  have h := chain_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 9)) (Q := T9) (R := T10)
    chain9_dvd LeanFormal.IUT.XiFPaper.S2565ChainComp3Actual.chain_dvd_9
  convert h using 1
  rw [← pow_mul]; norm_num

lemma chain11_dvd : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 11) - T11 := by
  have h := chain_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 10)) (Q := T10) (R := T11)
    chain10_dvd LeanFormal.IUT.XiFPaper.S2565ChainComp3Actual.chain_dvd_10
  convert h using 1
  rw [← pow_mul]; norm_num

lemma chain12_dvd : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 12) - T12 := by
  have h := chain_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 11)) (Q := T11) (R := T12)
    chain11_dvd LeanFormal.IUT.XiFPaper.S2565ChainComp3Actual.chain_dvd_11
  convert h using 1
  rw [← pow_mul]; norm_num

theorem hdvd : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 12) - X := by
  simpa [T12_eq_X] using chain12_dvd

lemma coprime4 : IsCoprime G ((X : (ZMod 613)[X]) ^ (613 ^ 4) - X) := by
  have hq : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 4) - T4 := chain4_dvd
  rcases hq with ⟨q, hq⟩
  have h := LeanFormal.IUT.XiFPaper.S2555Mod613BezoutActual.coprime_T4.add_mul_right_right q
  convert h using 1
  rw [← hq]; ring

lemma coprime6 : IsCoprime G ((X : (ZMod 613)[X]) ^ (613 ^ 6) - X) := by
  have hq : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 6) - T6 := chain6_dvd
  rcases hq with ⟨q, hq⟩
  have h := LeanFormal.IUT.XiFPaper.S2555Mod613BezoutActual.coprime_T6.add_mul_right_right q
  convert h using 1
  rw [← hq]; ring

theorem G_irreducible : Irreducible G :=
  LeanFormal.IUT.XiFPaper.S2550RabinCriterionActual.S2550irreducible_of_degree_twelve
    (K := ZMod 613) G_natDegree hdvd coprime4 coprime6

theorem F613_irreducible : Irreducible F613 := by
  have hunit : IsUnit (C (168 : ZMod 613)) := isUnit_C.mpr (by decide)
  have hassoc : Associated G F613 := by
    rw [G_eq_scaled]
    exact associated_unit_mul_left F613 (C (168 : ZMod 613)) hunit
  exact hassoc.irreducible G_irreducible

#print axioms F613_irreducible

end LeanFormal.IUT.XiFPaper.S2570F613IrreducibleActual
end
