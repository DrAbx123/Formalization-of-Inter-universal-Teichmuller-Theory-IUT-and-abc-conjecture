
/-
S2567: the explicit degree-twelve polynomial F613 is irreducible over ZMod 613.

The proof works in the quotient R = AdjoinRoot G, where G is the monic
normalization of F613 from S2554.  Writing x for the class of X:

* chain1_dvd : G ∣ X ^ 613 - T1 gives x ^ 613 = aeval x T1;
* freshman's dream in characteristic 613 gives, for every P,
  aeval x (P ^ 613) = aeval x (P.comp T1), hence
  G ∣ P ^ 613 - P.comp T1;
* the chain data T1, ..., T12 then gives G ∣ X ^ (613 ^ k) - Tk for
  k = 1, ..., 12 (this uses the S2565 chain-composition certificates
  G ∣ Tk.comp T1 - T(k+1)), and T12 = X gives G ∣ X ^ (613 ^ 12) - X;
* the coprimality certificates of S2555 promote to
  IsCoprime G (X ^ (613 ^ 4) - X) and IsCoprime G (X ^ (613 ^ 6) - X);
* the Rabin criterion of S2550 (degree twelve) yields Irreducible G, and
  G = C 168 * F613 with C 168 a unit yields Irreducible F613.

No axioms, no sorry, no native_decide.
-/

import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual
import tmp.sheaf.xif.paper.S2564Chain1IdentityActual
import tmp.sheaf.xif.paper.S2555Mod613BezoutActual
import tmp.sheaf.xif.paper.S2550RabinCriterionActual

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2567F613IrreducibleActual

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2564Chain1IdentityActual
open LeanFormal.IUT.XiFPaper.S2555Mod613BezoutActual
open LeanFormal.IUT.XiFPaper.S2550RabinCriterionActual

local instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

/-! ## 1. The quotient ring (ZMod 613)[X] / (G) and its root -/

/-- The quotient of (ZMod 613)[X] by the monic normalization G. -/
abbrev R : Type := AdjoinRoot G

/-- The class of X in the quotient. -/
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

/-- A divisibility G ∣ X ^ a - U reads x ^ a = U(x) in the quotient. -/
lemma aeval_X_pow_eq {a : ℕ} {U : (ZMod 613)[X]}
    (h : G ∣ (X : (ZMod 613)[X]) ^ a - U) : x ^ a = aeval x U := by
  have h0 : aeval x ((X : (ZMod 613)[X]) ^ a - U) = 0 := aeval_eq_zero_of_dvd h
  rw [map_sub, map_pow, aeval_X] at h0
  exact sub_eq_zero.mp h0

/-! ## 2. Freshman's dream and the composition identity -/

/-- Freshman's dream in characteristic 613: (P(x)) ^ 613 = P(x ^ 613). -/
lemma aeval_pow_card (q : (ZMod 613)[X]) :
    (aeval x q) ^ 613 = aeval (x ^ 613) q := by
  have hexp : q ^ 613 = Polynomial.expand (ZMod 613) 613 q := by
    have h := Polynomial.map_frobenius_expand (R := ZMod 613) (p := 613) q
    rw [ZMod.frobenius_zmod] at h
    simpa using h.symm
  calc (aeval x q) ^ 613 = aeval x (q ^ 613) := (map_pow _ _ _).symm
    _ = aeval x (Polynomial.expand (ZMod 613) 613 q) := by rw [hexp]
    _ = aeval (x ^ 613) q := Polynomial.expand_aeval 613 q x

/-- The Frobenius value of the root, from the chain-1 identity. -/
lemma hx613 : x ^ 613 = aeval x T1 := aeval_X_pow_eq chain1_dvd

/-- For every polynomial P, the class of P ^ 613 is the class of P.comp T1. -/
lemma aeval_pow_card_comp (q : (ZMod 613)[X]) :
    aeval x (q ^ 613) = aeval x (q.comp T1) := by
  calc aeval x (q ^ 613) = (aeval x q) ^ 613 := map_pow _ _ _
    _ = aeval (x ^ 613) q := aeval_pow_card q
    _ = aeval (aeval x T1) q := by rw [hx613]
    _ = aeval x (q.comp T1) := (aeval_comp x).symm

/-- The polynomial divisibility underlying the chain step. -/
lemma dvd_pow_card_sub_comp (q : (ZMod 613)[X]) :
    G ∣ q ^ 613 - q.comp T1 := by
  apply dvd_of_aeval_eq_zero
  rw [map_sub, aeval_pow_card_comp, sub_self]

/-! ## 3. Degree and coprimality helpers -/

lemma G_natDegree : G.natDegree = 12 := by
  unfold G
  compute_degree!

/-- If a is coprime to b and a ∣ c - b, then a is coprime to c. -/
lemma isCoprime_of_dvd_sub {a b c : (ZMod 613)[X]}
    (h : IsCoprime a b) (hbc : a ∣ c - b) : IsCoprime a c := by
  obtain ⟨u, v, huv⟩ := h
  obtain ⟨t, ht⟩ := hbc
  refine ⟨u - v * t, v, ?_⟩
  have hb : c - a * t = b := by rw [← ht]; ring
  calc (u - v * t) * a + v * c = u * a + v * (c - a * t) := by ring
    _ = u * a + v * b := by rw [hb]
    _ = 1 := huv

/-! ## 4. The induction step for the chain -/

/-- One step of the Frobenius chain: if G ∣ X ^ e - P and
G ∣ P.comp T1 - Q, then G ∣ X ^ (e * 613) - Q. -/
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
    ring
  have h4 : G ∣ ((X : (ZMod 613)[X]) ^ e) ^ 613 - Q := by
    have h := dvd_add h1 h3
    convert h using 1
    ring
  rw [← pow_mul] at h4
  exact h4

end LeanFormal.IUT.XiFPaper.S2567F613IrreducibleActual
end
