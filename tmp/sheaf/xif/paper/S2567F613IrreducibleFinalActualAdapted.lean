
import tmp.sheaf.xif.paper.S2564Chain1IdentityActual
import tmp.sheaf.xif.paper.S2566ChainComp1aActual
import tmp.sheaf.xif.paper.S2566ChainComp1bActual
import tmp.sheaf.xif.paper.S2566ChainComp1cActual
import tmp.sheaf.xif.paper.S2566ChainComp1dActual
import tmp.sheaf.xif.paper.S2565ChainComp2Actual
import tmp.sheaf.xif.paper.S2565ChainComp3Actual
import tmp.sheaf.xif.paper.S2555Mod613BezoutActual
import tmp.sheaf.xif.paper.S2550RabinCriterionActual

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2567F613IrreducibleFinalActualAdapted

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2564Chain1IdentityActual
open LeanFormal.IUT.XiFPaper.S2555Mod613BezoutActual
open LeanFormal.IUT.XiFPaper.S2550RabinCriterionActual

local instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

abbrev R : Type := AdjoinRoot G
noncomputable def x : R := AdjoinRoot.root G

lemma aeval_G : aeval x G = 0 := by
  unfold x
  rw [AdjoinRoot.aeval_eq]
  exact AdjoinRoot.mk_self

lemma aeval_eq_zero_of_dvd {q : (ZMod 613)[X]} (h : G ∣ q) : aeval x q = 0 := by
  obtain ⟨r, rfl⟩ := h
  rw [map_mul, aeval_G, zero_mul]

lemma dvd_of_aeval_eq_zero {q : (ZMod 613)[X]} (h : aeval x q = 0) : G ∣ q := by
  rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq]
  exact h

lemma aeval_X_pow_eq {a : ℕ} {U : (ZMod 613)[X]}
    (h : G ∣ (X : (ZMod 613)[X]) ^ a - U) : x ^ a = aeval x U := by
  have h0 : aeval x ((X : (ZMod 613)[X]) ^ a - U) = 0 := aeval_eq_zero_of_dvd h
  rw [map_sub, map_pow, aeval_X] at h0
  exact sub_eq_zero.mp h0

lemma aeval_pow_card (q : (ZMod 613)[X]) :
    (aeval x q) ^ 613 = aeval (x ^ 613) q := by
  have hexp : q ^ 613 = Polynomial.expand (ZMod 613) 613 q := by
    have h := Polynomial.map_frobenius_expand (R := ZMod 613) (p := 613) q
    rw [ZMod.frobenius_zmod] at h
    simpa using h.symm
  calc (aeval x q) ^ 613 = aeval x (q ^ 613) := (map_pow _ _ _).symm
    _ = aeval x (Polynomial.expand (ZMod 613) 613 q) := by rw [hexp]
    _ = aeval (x ^ 613) q := Polynomial.expand_aeval 613 q x

lemma hx613 : x ^ 613 = aeval x T1 := aeval_X_pow_eq chain1_dvd

lemma aeval_pow_card_comp (q : (ZMod 613)[X]) :
    aeval x (q ^ 613) = aeval x (q.comp T1) := by
  calc aeval x (q ^ 613) = (aeval x q) ^ 613 := map_pow _ _ _
    _ = aeval (x ^ 613) q := aeval_pow_card q
    _ = aeval (aeval x T1) q := by rw [hx613]
    _ = aeval x (q.comp T1) := (aeval_comp x).symm

lemma dvd_pow_card_sub_comp (q : (ZMod 613)[X]) :
    G ∣ q ^ 613 - q.comp T1 := by
  apply dvd_of_aeval_eq_zero
  rw [map_sub, aeval_pow_card_comp, sub_self]

lemma G_natDegree : G.natDegree = 12 := by
  unfold G
  compute_degree!

lemma isCoprime_of_dvd_sub {a b c : (ZMod 613)[X]}
    (h : IsCoprime a b) (hbc : a ∣ c - b) : IsCoprime a c := by
  obtain ⟨u, v, huv⟩ := h
  obtain ⟨t, ht⟩ := hbc
  refine ⟨u - v * t, v, ?_⟩
  have hb : c - a * t = b := by rw [← ht]; ring
  calc (u - v * t) * a + v * c = u * a + v * (c - a * t) := by ring
    _ = u * a + v * b := by rw [hb]
    _ = 1 := huv

/-! ## General chain step -/

lemma dvd_step {P Q : (ZMod 613)[X]} {e : ℕ}
    (hP : G ∣ (X : (ZMod 613)[X]) ^ e - P)
    (hPQ : G ∣ P.comp T1 - Q) :
    G ∣ (X : (ZMod 613)[X]) ^ (e * 613) - Q := by
  have h1 : G ∣ ((X : (ZMod 613)[X]) ^ e) ^ 613 - P ^ 613 :=
    hP.trans (sub_dvd_pow_sub_pow _ _ 613)
  have h2 : G ∣ P ^ 613 - P.comp T1 := dvd_pow_card_sub_comp P
  have h3 : G ∣ P ^ 613 - Q := by
    have h := dvd_add h2 hPQ
    convert h using 1
    abel
  have h4 : G ∣ ((X : (ZMod 613)[X]) ^ e) ^ 613 - Q := by
    have h := dvd_add h1 h3
    convert h using 1
    abel
  simpa [pow_mul] using h4

/-! ## Test the chain with placeholder comp facts -/


lemma G_dvd_X_pow_1_sub_T1 : G ∣ (X : (ZMod 613)[X]) ^ 613 ^ 1 - T1 := by
  simpa using chain1_dvd

lemma G_dvd_X_pow_2_sub_T2 : G ∣ (X : (ZMod 613)[X]) ^ 613 ^ 2 - T2 := by
  have h := dvd_step (P := T1) (Q := T2) (e := 613) chain1_dvd LeanFormal.IUT.XiFPaper.S2566ChainComp1aActual.chain_dvd_1
  simpa using h

lemma G_dvd_X_pow_3_sub_T3 : G ∣ (X : (ZMod 613)[X]) ^ 613 ^ 3 - T3 := by
  have h := dvd_step (P := T2) (Q := T3) (e := 613 ^ 2) G_dvd_X_pow_2_sub_T2 LeanFormal.IUT.XiFPaper.S2566ChainComp1bActual.chain_dvd_2
  simpa using h

lemma G_dvd_X_pow_4_sub_T4 : G ∣ (X : (ZMod 613)[X]) ^ 613 ^ 4 - T4 := by
  have h := dvd_step (P := T3) (Q := T4) (e := 613 ^ 3) G_dvd_X_pow_3_sub_T3 LeanFormal.IUT.XiFPaper.S2566ChainComp1cActual.chain_dvd_3
  simpa using h

lemma G_dvd_X_pow_5_sub_T5 : G ∣ (X : (ZMod 613)[X]) ^ 613 ^ 5 - T5 := by
  have h := dvd_step (P := T4) (Q := T5) (e := 613 ^ 4) G_dvd_X_pow_4_sub_T4 LeanFormal.IUT.XiFPaper.S2566ChainComp1dActual.chain_dvd_4
  simpa using h

lemma G_dvd_X_pow_6_sub_T6 : G ∣ (X : (ZMod 613)[X]) ^ 613 ^ 6 - T6 := by
  have h := dvd_step (P := T5) (Q := T6) (e := 613 ^ 5) G_dvd_X_pow_5_sub_T5 LeanFormal.IUT.XiFPaper.S2565ChainComp2Actual.chain_dvd_5
  simpa using h

lemma G_dvd_X_pow_7_sub_T7 : G ∣ (X : (ZMod 613)[X]) ^ 613 ^ 7 - T7 := by
  have h := dvd_step (P := T6) (Q := T7) (e := 613 ^ 6) G_dvd_X_pow_6_sub_T6 LeanFormal.IUT.XiFPaper.S2565ChainComp2Actual.chain_dvd_6
  simpa using h

lemma G_dvd_X_pow_8_sub_T8 : G ∣ (X : (ZMod 613)[X]) ^ 613 ^ 8 - T8 := by
  have h := dvd_step (P := T7) (Q := T8) (e := 613 ^ 7) G_dvd_X_pow_7_sub_T7 LeanFormal.IUT.XiFPaper.S2565ChainComp2Actual.chain_dvd_7
  simpa using h

lemma G_dvd_X_pow_9_sub_T9 : G ∣ (X : (ZMod 613)[X]) ^ 613 ^ 9 - T9 := by
  have h := dvd_step (P := T8) (Q := T9) (e := 613 ^ 8) G_dvd_X_pow_8_sub_T8 LeanFormal.IUT.XiFPaper.S2565ChainComp2Actual.chain_dvd_8
  simpa using h

lemma G_dvd_X_pow_10_sub_T10 : G ∣ (X : (ZMod 613)[X]) ^ 613 ^ 10 - T10 := by
  have h := dvd_step (P := T9) (Q := T10) (e := 613 ^ 9) G_dvd_X_pow_9_sub_T9 LeanFormal.IUT.XiFPaper.S2565ChainComp3Actual.chain_dvd_9
  simpa using h

lemma G_dvd_X_pow_11_sub_T11 : G ∣ (X : (ZMod 613)[X]) ^ 613 ^ 11 - T11 := by
  have h := dvd_step (P := T10) (Q := T11) (e := 613 ^ 10) G_dvd_X_pow_10_sub_T10 LeanFormal.IUT.XiFPaper.S2565ChainComp3Actual.chain_dvd_10
  simpa using h

lemma G_dvd_X_pow_12_sub_T12 : G ∣ (X : (ZMod 613)[X]) ^ 613 ^ 12 - T12 := by
  have h := dvd_step (P := T11) (Q := T12) (e := 613 ^ 11) G_dvd_X_pow_11_sub_T11 LeanFormal.IUT.XiFPaper.S2565ChainComp3Actual.chain_dvd_11
  simpa using h

lemma G_dvd_X_pow_12_sub_X : G ∣ (X : (ZMod 613)[X]) ^ 613 ^ 12 - X := by
  have h := G_dvd_X_pow_12_sub_T12
  rwa [T12_eq_X] at h

lemma coprime_X_pow_4_sub_X : IsCoprime G ((X : (ZMod 613)[X]) ^ 613 ^ 4 - X) := by
  have hsub : G ∣ ((X : (ZMod 613)[X]) ^ 613 ^ 4 - X) - (T4 - X) := by
    have heq : ((X : (ZMod 613)[X]) ^ 613 ^ 4 - X) - (T4 - X) =
        (X : (ZMod 613)[X]) ^ 613 ^ 4 - T4 := by abel
    rw [heq]
    exact G_dvd_X_pow_4_sub_T4
  exact isCoprime_of_dvd_sub coprime_T4 hsub

lemma coprime_X_pow_6_sub_X : IsCoprime G ((X : (ZMod 613)[X]) ^ 613 ^ 6 - X) := by
  have hsub : G ∣ ((X : (ZMod 613)[X]) ^ 613 ^ 6 - X) - (T6 - X) := by
    have heq : ((X : (ZMod 613)[X]) ^ 613 ^ 6 - X) - (T6 - X) =
        (X : (ZMod 613)[X]) ^ 613 ^ 6 - T6 := by abel
    rw [heq]
    exact G_dvd_X_pow_6_sub_T6
  exact isCoprime_of_dvd_sub coprime_T6 hsub

lemma card_ZMod : Nat.card (ZMod 613) = 613 := by
  rw [Nat.card_eq_fintype_card, ZMod.card]

theorem G_irreducible : Irreducible G := by
  apply S2550irreducible_of_degree_twelve (K := ZMod 613) (f := G) G_natDegree
  · rw [card_ZMod]
    exact G_dvd_X_pow_12_sub_X
  · rw [card_ZMod]
    exact coprime_X_pow_4_sub_X
  · rw [card_ZMod]
    exact coprime_X_pow_6_sub_X

theorem F613_irreducible : Irreducible F613 := by
  have hunit : IsUnit (C (168 : ZMod 613) : (ZMod 613)[X]) := by
    rw [isUnit_C]
    exact isUnit_iff_ne_zero.mpr (by decide)
  have hassoc : Associated G F613 := by
    rw [G_eq_scaled]
    exact associated_unit_mul_left F613 (C (168 : ZMod 613)) hunit
  exact hassoc.irreducible G_irreducible

end LeanFormal.IUT.XiFPaper.S2567F613IrreducibleFinalActualAdapted
end
