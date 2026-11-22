
import tmp.sheaf.xif.paper.S2564Chain1IdentityActual
import tmp.sheaf.xif.paper.S2566ChainComp1aActual
import tmp.sheaf.xif.paper.S2566ChainComp1bActual
import tmp.sheaf.xif.paper.S2566ChainComp1cActual
import tmp.sheaf.xif.paper.S2566ChainComp1dActual
import tmp.sheaf.xif.paper.S2565ChainComp2Actual
import tmp.sheaf.xif.paper.S2565ChainComp3Actual

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2567bStepProbe

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
  calc (u - v * t) * a + v * c = u * a + v * (c - a * t) := by abel
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
  rwa [pow_mul] at h4

/-! ## Test the chain with placeholder comp facts -/



#check dvd_step
#check dvd_pow_card_sub_comp

end LeanFormal.IUT.XiFPaper.S2567bStepProbe

end
