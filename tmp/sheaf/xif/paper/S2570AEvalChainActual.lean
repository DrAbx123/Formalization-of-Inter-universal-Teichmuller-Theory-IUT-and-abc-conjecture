import tmp.sheaf.xif.paper.S2569GdivActual
import tmp.sheaf.xif.paper.S2564Chain1IdentityActual
import tmp.sheaf.xif.paper.S2566ChainComp1aActual
import tmp.sheaf.xif.paper.S2566ChainComp1bActual
import tmp.sheaf.xif.paper.S2566ChainComp1cActual
import tmp.sheaf.xif.paper.S2566ChainComp1dActual
import tmp.sheaf.xif.paper.S2565ChainComp2Actual
import tmp.sheaf.xif.paper.S2565ChainComp3Actual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2570AEvalChainActual

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2568FreshmanActual

instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

private lemma G_ne_zero : G ≠ 0 := by
  intro h
  have h0 : G.natDegree = 0 := by rw [h, natDegree_zero]
  have h12 : G.natDegree = 12 := by unfold G; compute_degree!
  omega
private lemma G_natDegree : G.natDegree = 12 := by unfold G; compute_degree!

abbrev A := AdjoinRoot G
def x : A := AdjoinRoot.root G

private lemma A_nontrivial : Nontrivial A := AdjoinRoot.nontrivial (f := G) (by
  rw [Polynomial.degree_eq_natDegree G_ne_zero, G_natDegree]
  norm_num)
private lemma A_charP : CharP A 613 := by
  haveI := A_nontrivial
  exact CharP.of_ringHom_of_ne_zero (algebraMap (ZMod 613) A) 613 (by norm_num)

attribute [local instance] A_nontrivial A_charP

lemma hroot : aeval x T1 = x ^ 613 := by
  have h : aeval (AdjoinRoot.root G) ((X : (ZMod 613)[X]) ^ 613 - T1) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
    exact LeanFormal.IUT.XiFPaper.S2564Chain1IdentityActual.chain1_dvd
  rw [map_sub, map_pow, aeval_X, sub_eq_zero] at h
  exact h.symm

lemma aeval_step {P Q R : (ZMod 613)[X]}
    (h1 : aeval x P = aeval x Q) (h2 : G ∣ Q.comp T1 - R) :
    aeval x (P ^ 613) = aeval x R := by
  rw [map_pow, h1, aeval_pow_613, ← hroot, ← aeval_comp]
  have h2zero : aeval (AdjoinRoot.root G) (Q.comp T1 - R) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
    exact h2
  rw [map_sub] at h2zero
  exact sub_eq_zero.mp h2zero

lemma chain1_aeval : aeval x ((X : (ZMod 613)[X]) ^ 613) = aeval x T1 := by
  rw [map_pow, aeval_X, hroot]

lemma chain2_aeval : aeval x ((X : (ZMod 613)[X]) ^ (613 ^ 2)) = aeval x T2 := by
  have hpow : (X : (ZMod 613)[X]) ^ (613 ^ 2) = ((X : (ZMod 613)[X]) ^ 613) ^ 613 := by
    rw [← pow_mul]
    congr 1
  rw [hpow]
  exact aeval_step (P := (X : (ZMod 613)[X]) ^ 613) (Q := T1) (R := T2) chain1_aeval LeanFormal.IUT.XiFPaper.S2566ChainComp1aActual.chain_dvd_1

lemma chain3_aeval : aeval x ((X : (ZMod 613)[X]) ^ (613 ^ 3)) = aeval x T3 := by
  have hpow : (X : (ZMod 613)[X]) ^ (613 ^ 3) = ((X : (ZMod 613)[X]) ^ (613 ^ 2)) ^ 613 := by
    rw [← pow_mul]
    congr 1
  rw [hpow]
  exact aeval_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 2)) (Q := T2) (R := T3) chain2_aeval LeanFormal.IUT.XiFPaper.S2566ChainComp1bActual.chain_dvd_2

lemma chain4_aeval : aeval x ((X : (ZMod 613)[X]) ^ (613 ^ 4)) = aeval x T4 := by
  have hpow : (X : (ZMod 613)[X]) ^ (613 ^ 4) = ((X : (ZMod 613)[X]) ^ (613 ^ 3)) ^ 613 := by
    rw [← pow_mul]
    congr 1
  rw [hpow]
  exact aeval_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 3)) (Q := T3) (R := T4) chain3_aeval LeanFormal.IUT.XiFPaper.S2566ChainComp1cActual.chain_dvd_3

lemma chain5_aeval : aeval x ((X : (ZMod 613)[X]) ^ (613 ^ 5)) = aeval x T5 := by
  have hpow : (X : (ZMod 613)[X]) ^ (613 ^ 5) = ((X : (ZMod 613)[X]) ^ (613 ^ 4)) ^ 613 := by
    rw [← pow_mul]
    congr 1
  rw [hpow]
  exact aeval_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 4)) (Q := T4) (R := T5) chain4_aeval LeanFormal.IUT.XiFPaper.S2566ChainComp1dActual.chain_dvd_4

lemma chain6_aeval : aeval x ((X : (ZMod 613)[X]) ^ (613 ^ 6)) = aeval x T6 := by
  have hpow : (X : (ZMod 613)[X]) ^ (613 ^ 6) = ((X : (ZMod 613)[X]) ^ (613 ^ 5)) ^ 613 := by
    rw [← pow_mul]
    congr 1
  rw [hpow]
  exact aeval_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 5)) (Q := T5) (R := T6) chain5_aeval LeanFormal.IUT.XiFPaper.S2565ChainComp2Actual.chain_dvd_5

lemma chain7_aeval : aeval x ((X : (ZMod 613)[X]) ^ (613 ^ 7)) = aeval x T7 := by
  have hpow : (X : (ZMod 613)[X]) ^ (613 ^ 7) = ((X : (ZMod 613)[X]) ^ (613 ^ 6)) ^ 613 := by
    rw [← pow_mul]
    congr 1
  rw [hpow]
  exact aeval_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 6)) (Q := T6) (R := T7) chain6_aeval LeanFormal.IUT.XiFPaper.S2565ChainComp2Actual.chain_dvd_6

lemma chain8_aeval : aeval x ((X : (ZMod 613)[X]) ^ (613 ^ 8)) = aeval x T8 := by
  have hpow : (X : (ZMod 613)[X]) ^ (613 ^ 8) = ((X : (ZMod 613)[X]) ^ (613 ^ 7)) ^ 613 := by
    rw [← pow_mul]
    congr 1
  rw [hpow]
  exact aeval_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 7)) (Q := T7) (R := T8) chain7_aeval LeanFormal.IUT.XiFPaper.S2565ChainComp2Actual.chain_dvd_7

lemma chain9_aeval : aeval x ((X : (ZMod 613)[X]) ^ (613 ^ 9)) = aeval x T9 := by
  have hpow : (X : (ZMod 613)[X]) ^ (613 ^ 9) = ((X : (ZMod 613)[X]) ^ (613 ^ 8)) ^ 613 := by
    rw [← pow_mul]
    congr 1
  rw [hpow]
  exact aeval_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 8)) (Q := T8) (R := T9) chain8_aeval LeanFormal.IUT.XiFPaper.S2565ChainComp2Actual.chain_dvd_8

lemma chain10_aeval : aeval x ((X : (ZMod 613)[X]) ^ (613 ^ 10)) = aeval x T10 := by
  have hpow : (X : (ZMod 613)[X]) ^ (613 ^ 10) = ((X : (ZMod 613)[X]) ^ (613 ^ 9)) ^ 613 := by
    rw [← pow_mul]
    congr 1
  rw [hpow]
  exact aeval_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 9)) (Q := T9) (R := T10) chain9_aeval LeanFormal.IUT.XiFPaper.S2565ChainComp3Actual.chain_dvd_9

lemma chain11_aeval : aeval x ((X : (ZMod 613)[X]) ^ (613 ^ 11)) = aeval x T11 := by
  have hpow : (X : (ZMod 613)[X]) ^ (613 ^ 11) = ((X : (ZMod 613)[X]) ^ (613 ^ 10)) ^ 613 := by
    rw [← pow_mul]
    congr 1
  rw [hpow]
  exact aeval_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 10)) (Q := T10) (R := T11) chain10_aeval LeanFormal.IUT.XiFPaper.S2565ChainComp3Actual.chain_dvd_10

lemma chain12_aeval : aeval x ((X : (ZMod 613)[X]) ^ (613 ^ 12)) = aeval x T12 := by
  have hpow : (X : (ZMod 613)[X]) ^ (613 ^ 12) = ((X : (ZMod 613)[X]) ^ (613 ^ 11)) ^ 613 := by
    rw [← pow_mul]
    congr 1
  rw [hpow]
  exact aeval_step (P := (X : (ZMod 613)[X]) ^ (613 ^ 11)) (Q := T11) (R := T12) chain11_aeval LeanFormal.IUT.XiFPaper.S2565ChainComp3Actual.chain_dvd_11

lemma chain12_sub_X_aeval : aeval x ((X : (ZMod 613)[X]) ^ (613 ^ 12) - X) = 0 := by
  rw [map_sub, chain12_aeval, T12_eq_X, aeval_X, sub_self]

theorem G_dvd_pow_sub_X : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 12) - X := by
  rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq]
  exact chain12_sub_X_aeval

theorem G_dvd_pow4_sub_T4 : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 4) - T4 := by
  rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq]
  change aeval x ((X : (ZMod 613)[X]) ^ (613 ^ 4) - T4) = 0
  rw [map_sub, chain4_aeval, sub_self]

theorem G_dvd_pow6_sub_T6 : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 6) - T6 := by
  rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq]
  change aeval x ((X : (ZMod 613)[X]) ^ (613 ^ 6) - T6) = 0
  rw [map_sub, chain6_aeval, sub_self]

end LeanFormal.IUT.XiFPaper.S2570AEvalChainActual
end