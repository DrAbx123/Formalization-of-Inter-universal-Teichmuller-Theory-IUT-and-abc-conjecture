/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S2481PairTransitiveHardActual

/-!
# S2540: the degree-twelve mod-613 residue certificate

This file inhabits the residue certificate

  Irreducible (S2132Psi5Z.map (Int.castRingHom (ZMod 613)))

that was isolated as the plain proposition S2481ResidueCertificate in
tmp.sheaf.xif.paper.S2481PairTransitiveHardActual.  It is the finite-field input
for the Dedekind--Frobenius route to a residue-degree-twelve prime of the
degree-twelve field of psi_5.

## Organisation

1. S2540F is the explicit reduction of S2132Psi5Z modulo 613, and
   S2540F_eq_target identifies the two polynomials coefficientwise.
2. S2540irreducible_of_degree_twelve is the Rabin criterion in degree 12: if f
   has degree 12, divides X^(q^12) - X, and is coprime to X^(q^4) - X and
   X^(q^6) - X, then f is irreducible.
3. The finite computation: S2540T1 = X^613 mod S2540F is obtained by a
   binary-power chain (certificates S2540cert16 ... S2540certT1); the Frobenius
   iterates S2540T_k = X^(613^k) mod S2540F are obtained by repeatedly
   substituting S2540T1, using the fixed table S2540D_i = S2540T1^i mod S2540F.
   The chain ends with S2540spec12 : x^(613^12) = x, i.e. S2540F divides
   X^(613^12) - X.
4. The coprimality certificates are the explicit Bezout identities
   S2540certP4 and S2540certP6.

All certificates are explicit coefficientwise polynomial identities over
ZMod 613; the development contains no proof placeholders and no additional
assumptions.

## Numerical content of the certificate (computed independently)

The polynomial S2540F has degree 12 over GF(613).  The reduction data below was
computed with exact integer modular arithmetic before being written out:

* S2540T1  = X^613 mod S2540F,
* S2540T_k = X^(613^k) mod S2540F for k = 2, ..., 11, and S2540T12 = X,
* S2540D_i = S2540T1^i mod S2540F for i = 0, ..., 11,
* S2540P4 * F + S2540Q4 * (S2540T4 - X) = 1,
* S2540P6 * F + S2540Q6 * (S2540T6 - X) = 1.

Consequently X^(613^12) = X in GF(613)[X]/(S2540F), and the gcds of S2540F with
X^(613^4) - X and X^(613^6) - X are both one, so the degree-twelve Rabin
criterion applies.
-/

noncomputable section
open Polynomial

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2540Mod613CertificateActual

open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual

local instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

/-! ## 1. The concrete polynomial -/

/-- The reduction modulo 613 of the degree-twelve integer model S2132Psi5Z. -/
def S2540F : (ZMod 613)[X] :=
  monomial 0 (415 : ZMod 613) +
  monomial 2 (203 : ZMod 613) +
  monomial 3 (163 : ZMod 613) +
  monomial 4 (443 : ZMod 613) +
  monomial 5 (408 : ZMod 613) +
  monomial 6 (580 : ZMod 613) +
  monomial 7 (577 : ZMod 613) +
  monomial 8 (401 : ZMod 613) +
  monomial 9 (604 : ZMod 613) +
  monomial 10 (461 : ZMod 613) +
  monomial 11 (60 : ZMod 613) +
  monomial 12 (478 : ZMod 613)


/-- The concrete polynomial is the reduction of the S2132Psi5Z integer model
that occurs in S2481ResidueCertificate. -/
theorem S2540F_eq_target : S2132Psi5Z.map (Int.castRingHom (ZMod 613)) = S2540F := by
  ext n
  by_cases hn : n ≤ 12
  · interval_cases n <;>
      (simp [S2132Psi5Z, S2540F, Polynomial.coeff_add, Polynomial.coeff_C,
        Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one,
        Polynomial.coeff_monomial] <;> decide)
  · have h1 : (S2132Psi5Z.map (Int.castRingHom (ZMod 613))).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have hle : (S2132Psi5Z.map (Int.castRingHom (ZMod 613))).natDegree ≤
          S2132Psi5Z.natDegree := Polynomial.natDegree_map_le
      have h12 : S2132Psi5Z.natDegree = 12 := by
        unfold S2132Psi5Z
        compute_degree!
      omega
    have h2 : S2540F.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h12 : S2540F.natDegree = 12 := by
        unfold S2540F
        compute_degree!
      omega
    rw [h1, h2]

lemma S2540F_natDegree : S2540F.natDegree = 12 := by
  unfold S2540F
  compute_degree!

lemma S2540F_ne_zero : S2540F ≠ 0 := by
  intro h
  have hd := S2540F_natDegree
  rw [h, natDegree_zero] at hd
  omega

/-! ## 2. The Rabin criterion in degree twelve -/

/-- If d divides m then X^(q^d) - X divides X^(q^m) - X. -/
lemma S2540X_pow_dvd {K : Type*} [CommRing K] {d m : ℕ} (h : d ∣ m) :
    ((X : K[X]) ^ Nat.card K ^ d - X) ∣ ((X : K[X]) ^ Nat.card K ^ m - X) :=
  dvd_pow_pow_sub_self_of_dvd (r := (X : K[X])) (p := Nat.card K) h

/-- Rabin criterion, degree 12.  If f has degree twelve, every root of f lies in
GF(q^12), and f has no root in GF(q^4) or GF(q^6), then f is irreducible. -/
theorem S2540irreducible_of_degree_twelve {K : Type*} [Field K] [Fintype K] {f : K[X]}
    (hdeg : f.natDegree = 12)
    (hdvd : f ∣ (X : K[X]) ^ Nat.card K ^ 12 - X)
    (h4 : IsCoprime f ((X : K[X]) ^ Nat.card K ^ 4 - X))
    (h6 : IsCoprime f ((X : K[X]) ^ Nat.card K ^ 6 - X)) :
    Irreducible f := by
  by_contra hf
  have hf0 : f ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hfunit : ¬ IsUnit f := by
    intro hu
    have h0 := natDegree_eq_zero_of_isUnit hu
    omega
  obtain ⟨g, hg_irr, hg_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hfunit hf0
  have hg_dvd_E : g ∣ (X : K[X]) ^ Nat.card K ^ 12 - X := hg_dvd.trans hdvd
  have hdvd12 : g.natDegree ∣ 12 :=
    Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hg_irr hg_dvd_E
  have hgpos : 0 < g.natDegree := Irreducible.natDegree_pos hg_irr
  have hgle : g.natDegree ≤ 12 := by
    rw [← hdeg]
    exact natDegree_le_of_dvd hg_dvd hf0
  have hgne : g.natDegree ≠ 12 := by
    intro h12
    have hassoc : Associated g f := associated_of_dvd_of_natDegree_le hg_dvd hf0 (by omega)
    exact hf (hassoc.irreducible hg_irr)
  set d := g.natDegree with hddef
  have hdvd' : d ∣ 12 := by simpa [hddef] using hdvd12
  have hlt' : d < 12 := by simpa [hddef] using lt_of_le_of_ne hgle hgne
  have hpos' : 0 < d := by simpa [hddef] using hgpos
  have hcases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 6 := by
    interval_cases d <;> norm_num at hdvd' <;> norm_num
  rcases hcases with h1 | h2 | h3 | h4d | h6d
  · have hgd : g.natDegree = 1 := by omega
    have hg1 : g ∣ (X : K[X]) ^ Nat.card K ^ g.natDegree - X :=
      irreducible_dvd_X_pow_card_pow_sub_X hg_irr
    have hg1' : g ∣ (X : K[X]) ^ Nat.card K ^ 1 - X := by simpa [hgd] using hg1
    have hg6 : g ∣ (X : K[X]) ^ Nat.card K ^ 6 - X :=
      hg1'.trans (S2540X_pow_dvd (K := K) (d := 1) (m := 6) (by norm_num))
    exact hg_irr.not_isUnit (h6.isUnit_of_dvd' hg_dvd hg6)
  · have hgd : g.natDegree = 2 := by omega
    have hg2 : g ∣ (X : K[X]) ^ Nat.card K ^ 2 - X := by
      simpa [hgd] using irreducible_dvd_X_pow_card_pow_sub_X hg_irr
    have hg6 : g ∣ (X : K[X]) ^ Nat.card K ^ 6 - X :=
      hg2.trans (S2540X_pow_dvd (K := K) (d := 2) (m := 6) (by norm_num))
    exact hg_irr.not_isUnit (h6.isUnit_of_dvd' hg_dvd hg6)
  · have hgd : g.natDegree = 3 := by omega
    have hg3 : g ∣ (X : K[X]) ^ Nat.card K ^ 3 - X := by
      simpa [hgd] using irreducible_dvd_X_pow_card_pow_sub_X hg_irr
    have hg6 : g ∣ (X : K[X]) ^ Nat.card K ^ 6 - X :=
      hg3.trans (S2540X_pow_dvd (K := K) (d := 3) (m := 6) (by norm_num))
    exact hg_irr.not_isUnit (h6.isUnit_of_dvd' hg_dvd hg6)
  · have hgd : g.natDegree = 4 := by omega
    have hg4 : g ∣ (X : K[X]) ^ Nat.card K ^ 4 - X := by
      simpa [hgd] using irreducible_dvd_X_pow_card_pow_sub_X hg_irr
    exact hg_irr.not_isUnit (h4.isUnit_of_dvd' hg_dvd hg4)
  · have hgd : g.natDegree = 6 := by omega
    have hg6 : g ∣ (X : K[X]) ^ Nat.card K ^ 6 - X := by
      simpa [hgd] using irreducible_dvd_X_pow_card_pow_sub_X hg_irr
    exact hg_irr.not_isUnit (h6.isUnit_of_dvd' hg_dvd hg6)

/-! ## 3. The quotient ring and its Frobenius calculus -/

/-- The quotient of (ZMod 613)[X] by the concrete polynomial. -/
abbrev S2540R : Type := AdjoinRoot S2540F

/-- The class of X. -/
noncomputable def S2540x : S2540R := AdjoinRoot.root S2540F

lemma S2540aeval_F : aeval S2540x S2540F = 0 := by
  unfold S2540x
  rw [AdjoinRoot.aeval_eq]
  exact AdjoinRoot.mk_self

instance S2540instCharP : CharP S2540R 613 := by
  have hdeg0 : S2540F.degree ≠ 0 := by
    rw [degree_eq_natDegree S2540F_ne_zero, S2540F_natDegree]
    norm_num
  have hinj : Function.Injective (algebraMap (ZMod 613) S2540R) := by
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.of.injective_of_degree_ne_zero hdeg0
  exact charP_of_injective_algebraMap hinj 613

lemma S2540aeval_eq_zero_of_dvd {q : (ZMod 613)[X]} (h : S2540F ∣ q) :
    aeval S2540x q = 0 := by
  obtain ⟨r, rfl⟩ := h
  rw [map_mul, S2540aeval_F, zero_mul]

lemma S2540dvd_of_aeval_eq_zero {q : (ZMod 613)[X]} (h : aeval S2540x q = 0) :
    S2540F ∣ q := by
  rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq]
  exact h

/-- One step of the reduction chain. -/
lemma S2540dvd_pow_add {a b : ℕ} {U V W S : (ZMod 613)[X]}
    (hUV : U * V - W = S2540F * S)
    (hU : S2540F ∣ (X : (ZMod 613)[X]) ^ a - U)
    (hV : S2540F ∣ (X : (ZMod 613)[X]) ^ b - V) :
    S2540F ∣ (X : (ZMod 613)[X]) ^ (a + b) - W := by
  have key : (X : (ZMod 613)[X]) ^ (a + b) - W =
      ((X : (ZMod 613)[X]) ^ b - V) * (X : (ZMod 613)[X]) ^ a +
      V * ((X : (ZMod 613)[X]) ^ a - U) + (U * V - W) := by
    rw [pow_add]; ring
  rw [key, hUV]
  exact dvd_add (dvd_add (hV.mul_right _) (hU.mul_left _)) (dvd_mul_right _ _)

/-- A divisibility S2540F ∣ X^a - U gives the ring identity x^a = U(x). -/
lemma S2540aeval_X_pow_eq {a : ℕ} {U : (ZMod 613)[X]}
    (h : S2540F ∣ (X : (ZMod 613)[X]) ^ a - U) : S2540x ^ a = aeval S2540x U := by
  have h0 : aeval S2540x ((X : (ZMod 613)[X]) ^ a - U) = 0 := S2540aeval_eq_zero_of_dvd h
  rw [map_sub, map_pow, Polynomial.aeval_X] at h0
  exact sub_eq_zero.mp h0

/-- The coefficient expansion of aeval. -/
lemma S2540aeval_eq_sum_range {R : Type*} [CommRing R] [Algebra (ZMod 613) R]
    (x : R) (q : (ZMod 613)[X]) (n : ℕ) (hq : q.natDegree < n) :
    aeval x q = ∑ i ∈ Finset.range n, algebraMap (ZMod 613) R (q.coeff i) * x ^ i := by
  conv_lhs => rw [q.as_sum_range' n hq]
  simp [map_sum, aeval_monomial]

/-- Freshman's dream: (aeval x q)^613 = aeval (x^613) q. -/
lemma S2540aeval_pow_char (x : S2540R) (q : (ZMod 613)[X]) :
    (aeval x q) ^ 613 = aeval (x ^ 613) q := by
  have hdeg : q.natDegree < q.natDegree + 1 := Nat.lt_succ_self q.natDegree
  rw [S2540aeval_eq_sum_range x q (q.natDegree + 1) hdeg,
    S2540aeval_eq_sum_range (x ^ 613) q (q.natDegree + 1) hdeg]
  change (∑ i ∈ Finset.range (q.natDegree + 1),
      algebraMap (ZMod 613) S2540R (q.coeff i) * x ^ i) ^ (613 ^ 1) =
    ∑ i ∈ Finset.range (q.natDegree + 1),
      algebraMap (ZMod 613) S2540R (q.coeff i) * (x ^ 613) ^ i
  rw [sum_pow_char_pow]
  simp only [pow_one]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_pow]
  have hcoeff : (algebraMap (ZMod 613) S2540R (q.coeff i)) ^ 613 =
      algebraMap (ZMod 613) S2540R (q.coeff i) := by
    rw [← map_pow]
    congr 1
    simpa using (ZMod.pow_card_pow (p := 613) (n := 1) (x := q.coeff i))
  rw [hcoeff]
  conv_lhs => rw [← pow_mul]
  conv_rhs => rw [← pow_mul]
  rw [Nat.mul_comm]

/-- Substituting the Frobenius table into a polynomial. -/
lemma S2540aeval_comp_sum {Q P : (ZMod 613)[X]} {Dfun : ℕ → (ZMod 613)[X]}
    {W : (ZMod 613)[X]}
    (hP : P.natDegree < 12)
    (hD : ∀ i < 12, aeval S2540x (Dfun i) = (aeval S2540x Q) ^ i)
    (hW : (∑ i ∈ Finset.range 12, C (P.coeff i) * Dfun i) = W) :
    aeval (aeval S2540x Q) P = aeval S2540x W := by
  calc aeval (aeval S2540x Q) P
      = ∑ i ∈ Finset.range 12,
          algebraMap (ZMod 613) S2540R (P.coeff i) * (aeval S2540x Q) ^ i :=
        S2540aeval_eq_sum_range _ P 12 hP
    _ = ∑ i ∈ Finset.range 12, aeval S2540x (C (P.coeff i) * Dfun i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Polynomial.aeval_mul, Polynomial.aeval_C, hD i (Finset.mem_range.mp hi)]
    _ = aeval S2540x (∑ i ∈ Finset.range 12, C (P.coeff i) * Dfun i) := by
        simp only [map_sum]
    _ = aeval S2540x W := by rw [hW]

/-- Coprimality is preserved by adding a multiple of the first argument. -/
lemma S2540isCoprime_of_dvd_sub {a b c : (ZMod 613)[X]}
    (h : IsCoprime a b) (hbc : a ∣ c - b) : IsCoprime a c := by
  obtain ⟨u, v, huv⟩ := h
  obtain ⟨t, ht⟩ := hbc
  refine ⟨u - v * t, v, ?_⟩
  have hb : c - a * t = b := by rw [← ht]; ring
  calc (u - v * t) * a + v * c = u * a + v * (c - a * t) := by ring
    _ = u * a + v * b := by rw [hb]
    _ = 1 := huv

/-! ## 4. The certificate data -/

/-- X^1. -/
def S2540A1 : (ZMod 613)[X] := X

/-- X^4. -/
def S2540A4 : (ZMod 613)[X] := X ^ 4

/-- X^16 reduced modulo S2540F -/
def S2540A16 : (ZMod 613)[X] :=
  monomial 0 (185 : ZMod 613) +
  monomial 1 (32 : ZMod 613) +
  monomial 2 (172 : ZMod 613) +
  monomial 3 (342 : ZMod 613) +
  monomial 4 (336 : ZMod 613) +
  monomial 5 (17 : ZMod 613) +
  monomial 6 (146 : ZMod 613) +
  monomial 7 (47 : ZMod 613) +
  monomial 8 (16 : ZMod 613) +
  monomial 9 (374 : ZMod 613) +
  monomial 10 (399 : ZMod 613) +
  monomial 11 (171 : ZMod 613)

/-- X^32 reduced modulo S2540F -/
def S2540A32 : (ZMod 613)[X] :=
  monomial 0 (250 : ZMod 613) +
  monomial 1 (434 : ZMod 613) +
  monomial 2 (263 : ZMod 613) +
  monomial 3 (247 : ZMod 613) +
  monomial 4 (67 : ZMod 613) +
  monomial 5 (526 : ZMod 613) +
  monomial 6 (554 : ZMod 613) +
  monomial 7 (241 : ZMod 613) +
  monomial 8 (427 : ZMod 613) +
  monomial 9 (352 : ZMod 613) +
  monomial 10 (495 : ZMod 613) +
  monomial 11 (281 : ZMod 613)

/-- X^64 reduced modulo S2540F -/
def S2540A64 : (ZMod 613)[X] :=
  monomial 0 (125 : ZMod 613) +
  monomial 1 (535 : ZMod 613) +
  monomial 2 (504 : ZMod 613) +
  monomial 3 (404 : ZMod 613) +
  monomial 4 (43 : ZMod 613) +
  monomial 5 (384 : ZMod 613) +
  monomial 6 (264 : ZMod 613) +
  monomial 7 (174 : ZMod 613) +
  monomial 8 (356 : ZMod 613) +
  monomial 9 (458 : ZMod 613) +
  monomial 10 (570 : ZMod 613) +
  monomial 11 (241 : ZMod 613)

/-- X^128 reduced modulo S2540F -/
def S2540A128 : (ZMod 613)[X] :=
  monomial 0 (354 : ZMod 613) +
  monomial 1 (328 : ZMod 613) +
  monomial 2 (372 : ZMod 613) +
  monomial 3 (268 : ZMod 613) +
  monomial 4 (59 : ZMod 613) +
  monomial 5 (562 : ZMod 613) +
  monomial 6 (134 : ZMod 613) +
  monomial 7 (212 : ZMod 613) +
  monomial 8 (396 : ZMod 613) +
  monomial 9 (389 : ZMod 613) +
  monomial 10 (408 : ZMod 613) +
  monomial 11 (89 : ZMod 613)

/-- X^256 reduced modulo S2540F -/
def S2540A256 : (ZMod 613)[X] :=
  monomial 0 (195 : ZMod 613) +
  monomial 1 (557 : ZMod 613) +
  monomial 2 (263 : ZMod 613) +
  monomial 3 (530 : ZMod 613) +
  monomial 4 (332 : ZMod 613) +
  monomial 5 (439 : ZMod 613) +
  monomial 6 (103 : ZMod 613) +
  monomial 7 (498 : ZMod 613) +
  monomial 8 (541 : ZMod 613) +
  monomial 9 (14 : ZMod 613) +
  monomial 10 (307 : ZMod 613) +
  monomial 11 (574 : ZMod 613)

/-- X^512 reduced modulo S2540F -/
def S2540A512 : (ZMod 613)[X] :=
  monomial 0 (443 : ZMod 613) +
  monomial 1 (203 : ZMod 613) +
  monomial 2 (124 : ZMod 613) +
  monomial 3 (141 : ZMod 613) +
  monomial 4 (455 : ZMod 613) +
  monomial 5 (565 : ZMod 613) +
  monomial 6 (202 : ZMod 613) +
  monomial 7 (219 : ZMod 613) +
  monomial 8 (52 : ZMod 613) +
  monomial 9 (288 : ZMod 613) +
  monomial 10 (191 : ZMod 613) +
  monomial 11 (259 : ZMod 613)

/-- X^512 * X^64 reduced modulo S2540F -/
def S2540M1 : (ZMod 613)[X] :=
  monomial 0 (37 : ZMod 613) +
  monomial 1 (40 : ZMod 613) +
  monomial 2 (315 : ZMod 613) +
  monomial 3 (587 : ZMod 613) +
  monomial 4 (458 : ZMod 613) +
  monomial 5 (130 : ZMod 613) +
  monomial 6 (258 : ZMod 613) +
  monomial 7 (514 : ZMod 613) +
  monomial 8 (448 : ZMod 613) +
  monomial 9 (118 : ZMod 613) +
  monomial 10 (125 : ZMod 613) +
  monomial 11 (157 : ZMod 613)

/-- X^576 * X^32 reduced modulo S2540F -/
def S2540M2 : (ZMod 613)[X] :=
  monomial 0 (599 : ZMod 613) +
  monomial 1 (411 : ZMod 613) +
  monomial 2 (525 : ZMod 613) +
  monomial 3 (116 : ZMod 613) +
  monomial 4 (583 : ZMod 613) +
  monomial 5 (106 : ZMod 613) +
  monomial 6 (592 : ZMod 613) +
  monomial 7 (427 : ZMod 613) +
  monomial 8 (238 : ZMod 613) +
  monomial 9 (204 : ZMod 613) +
  monomial 10 (115 : ZMod 613) +
  monomial 11 (31 : ZMod 613)

/-- X^608 * X^4 reduced modulo S2540F -/
def S2540M3 : (ZMod 613)[X] :=
  monomial 0 (160 : ZMod 613) +
  monomial 1 (376 : ZMod 613) +
  monomial 2 (438 : ZMod 613) +
  monomial 3 (511 : ZMod 613) +
  monomial 4 (202 : ZMod 613) +
  monomial 5 (180 : ZMod 613) +
  monomial 6 (87 : ZMod 613) +
  monomial 7 (466 : ZMod 613) +
  monomial 8 (168 : ZMod 613) +
  monomial 9 (50 : ZMod 613) +
  monomial 10 (459 : ZMod 613) +
  monomial 11 (39 : ZMod 613)

/-- X^613 reduced modulo S2540F: the Frobenius polynomial -/
def S2540T1 : (ZMod 613)[X] :=
  monomial 0 (188 : ZMod 613) +
  monomial 1 (160 : ZMod 613) +
  monomial 2 (530 : ZMod 613) +
  monomial 3 (308 : ZMod 613) +
  monomial 4 (530 : ZMod 613) +
  monomial 5 (279 : ZMod 613) +
  monomial 6 (7 : ZMod 613) +
  monomial 7 (567 : ZMod 613) +
  monomial 8 (432 : ZMod 613) +
  monomial 9 (288 : ZMod 613) +
  monomial 10 (442 : ZMod 613) +
  monomial 11 (272 : ZMod 613)

/-- cofactor of the X^16 certificate -/
def S2540S16 : (ZMod 613)[X] :=
  monomial 0 (487 : ZMod 613) +
  monomial 1 (124 : ZMod 613) +
  monomial 2 (398 : ZMod 613) +
  monomial 3 (279 : ZMod 613) +
  monomial 4 (168 : ZMod 613)

/-- cofactor of the X^32 certificate -/
def S2540S32 : (ZMod 613)[X] :=
  monomial 0 (525 : ZMod 613) +
  monomial 1 (91 : ZMod 613) +
  monomial 2 (213 : ZMod 613) +
  monomial 3 (411 : ZMod 613) +
  monomial 4 (438 : ZMod 613) +
  monomial 5 (497 : ZMod 613) +
  monomial 6 (431 : ZMod 613) +
  monomial 7 (571 : ZMod 613) +
  monomial 8 (98 : ZMod 613) +
  monomial 9 (405 : ZMod 613) +
  monomial 10 (519 : ZMod 613)

/-- cofactor of the X^64 certificate -/
def S2540S64 : (ZMod 613)[X] :=
  monomial 0 (202 : ZMod 613) +
  monomial 1 (12 : ZMod 613) +
  monomial 2 (136 : ZMod 613) +
  monomial 3 (51 : ZMod 613) +
  monomial 4 (28 : ZMod 613) +
  monomial 5 (328 : ZMod 613) +
  monomial 6 (133 : ZMod 613) +
  monomial 7 (241 : ZMod 613) +
  monomial 8 (483 : ZMod 613) +
  monomial 9 (312 : ZMod 613) +
  monomial 10 (128 : ZMod 613)

/-- cofactor of the X^128 certificate -/
def S2540S128 : (ZMod 613)[X] :=
  monomial 0 (56 : ZMod 613) +
  monomial 1 (515 : ZMod 613) +
  monomial 2 (160 : ZMod 613) +
  monomial 3 (577 : ZMod 613) +
  monomial 4 (382 : ZMod 613) +
  monomial 6 (488 : ZMod 613) +
  monomial 7 (243 : ZMod 613) +
  monomial 8 (232 : ZMod 613) +
  monomial 9 (429 : ZMod 613) +
  monomial 10 (487 : ZMod 613)

/-- cofactor of the X^256 certificate -/
def S2540S256 : (ZMod 613)[X] :=
  monomial 0 (269 : ZMod 613) +
  monomial 1 (412 : ZMod 613) +
  monomial 2 (385 : ZMod 613) +
  monomial 3 (174 : ZMod 613) +
  monomial 4 (326 : ZMod 613) +
  monomial 5 (582 : ZMod 613) +
  monomial 6 (478 : ZMod 613) +
  monomial 7 (261 : ZMod 613) +
  monomial 8 (540 : ZMod 613) +
  monomial 9 (387 : ZMod 613) +
  monomial 10 (518 : ZMod 613)

/-- cofactor of the X^512 certificate -/
def S2540S512 : (ZMod 613)[X] :=
  monomial 0 (417 : ZMod 613) +
  monomial 1 (133 : ZMod 613) +
  monomial 2 (498 : ZMod 613) +
  monomial 3 (418 : ZMod 613) +
  monomial 4 (598 : ZMod 613) +
  monomial 5 (483 : ZMod 613) +
  monomial 6 (545 : ZMod 613) +
  monomial 7 (413 : ZMod 613) +
  monomial 8 (353 : ZMod 613) +
  monomial 9 (354 : ZMod 613) +
  monomial 10 (520 : ZMod 613)

/-- cofactor of the X^576 certificate -/
def S2540SM1 : (ZMod 613)[X] :=
  monomial 0 (575 : ZMod 613) +
  monomial 1 (93 : ZMod 613) +
  monomial 2 (202 : ZMod 613) +
  monomial 3 (244 : ZMod 613) +
  monomial 4 (298 : ZMod 613) +
  monomial 5 (523 : ZMod 613) +
  monomial 6 (554 : ZMod 613) +
  monomial 7 (47 : ZMod 613) +
  monomial 8 (87 : ZMod 613) +
  monomial 9 (257 : ZMod 613) +
  monomial 10 (414 : ZMod 613)

/-- cofactor of the X^608 certificate -/
def S2540SM2 : (ZMod 613)[X] :=
  monomial 0 (269 : ZMod 613) +
  monomial 1 (307 : ZMod 613) +
  monomial 2 (199 : ZMod 613) +
  monomial 3 (526 : ZMod 613) +
  monomial 4 (239 : ZMod 613) +
  monomial 5 (483 : ZMod 613) +
  monomial 6 (403 : ZMod 613) +
  monomial 7 (578 : ZMod 613) +
  monomial 8 (126 : ZMod 613) +
  monomial 9 (311 : ZMod 613) +
  monomial 10 (486 : ZMod 613)

/-- cofactor of the X^612 certificate -/
def S2540SM3 : (ZMod 613)[X] :=
  monomial 0 (7 : ZMod 613) +
  monomial 1 (231 : ZMod 613) +
  monomial 2 (384 : ZMod 613) +
  monomial 3 (304 : ZMod 613)

/-- cofactor of the X^613 certificate -/
def S2540ST1 : (ZMod 613)[X] :=
  monomial 0 (422 : ZMod 613)

/-- S2540T1^0 = 1. -/
def S2540D0 : (ZMod 613)[X] := monomial 0 (1 : ZMod 613)

/-- S2540T1^1 = S2540T1. -/
def S2540D1 : (ZMod 613)[X] := S2540T1

/-- S2540T1^2 reduced modulo S2540F -/
def S2540D2 : (ZMod 613)[X] :=
  monomial 0 (341 : ZMod 613) +
  monomial 1 (188 : ZMod 613) +
  monomial 2 (266 : ZMod 613) +
  monomial 3 (274 : ZMod 613) +
  monomial 4 (408 : ZMod 613) +
  monomial 5 (154 : ZMod 613) +
  monomial 6 (48 : ZMod 613) +
  monomial 7 (3 : ZMod 613) +
  monomial 8 (457 : ZMod 613) +
  monomial 9 (18 : ZMod 613) +
  monomial 10 (120 : ZMod 613) +
  monomial 11 (507 : ZMod 613)

/-- S2540T1^3 reduced modulo S2540F -/
def S2540D3 : (ZMod 613)[X] :=
  monomial 0 (444 : ZMod 613) +
  monomial 1 (18 : ZMod 613) +
  monomial 2 (203 : ZMod 613) +
  monomial 3 (104 : ZMod 613) +
  monomial 4 (12 : ZMod 613) +
  monomial 5 (511 : ZMod 613) +
  monomial 6 (321 : ZMod 613) +
  monomial 7 (402 : ZMod 613) +
  monomial 8 (599 : ZMod 613) +
  monomial 9 (440 : ZMod 613) +
  monomial 10 (513 : ZMod 613) +
  monomial 11 (277 : ZMod 613)

/-- S2540T1^4 reduced modulo S2540F -/
def S2540D4 : (ZMod 613)[X] :=
  monomial 0 (450 : ZMod 613) +
  monomial 1 (303 : ZMod 613) +
  monomial 2 (14 : ZMod 613) +
  monomial 3 (145 : ZMod 613) +
  monomial 4 (313 : ZMod 613) +
  monomial 5 (486 : ZMod 613) +
  monomial 6 (225 : ZMod 613) +
  monomial 7 (9 : ZMod 613) +
  monomial 8 (507 : ZMod 613) +
  monomial 9 (142 : ZMod 613) +
  monomial 10 (147 : ZMod 613) +
  monomial 11 (573 : ZMod 613)

/-- S2540T1^5 reduced modulo S2540F -/
def S2540D5 : (ZMod 613)[X] :=
  monomial 0 (324 : ZMod 613) +
  monomial 1 (423 : ZMod 613) +
  monomial 2 (512 : ZMod 613) +
  monomial 3 (213 : ZMod 613) +
  monomial 4 (330 : ZMod 613) +
  monomial 5 (479 : ZMod 613) +
  monomial 6 (243 : ZMod 613) +
  monomial 7 (443 : ZMod 613) +
  monomial 8 (95 : ZMod 613) +
  monomial 9 (179 : ZMod 613) +
  monomial 10 (11 : ZMod 613) +
  monomial 11 (189 : ZMod 613)

/-- S2540T1^6 reduced modulo S2540F -/
def S2540D6 : (ZMod 613)[X] :=
  monomial 0 (229 : ZMod 613) +
  monomial 1 (433 : ZMod 613) +
  monomial 2 (251 : ZMod 613) +
  monomial 3 (268 : ZMod 613) +
  monomial 4 (89 : ZMod 613) +
  monomial 5 (84 : ZMod 613) +
  monomial 6 (509 : ZMod 613) +
  monomial 7 (90 : ZMod 613) +
  monomial 8 (273 : ZMod 613) +
  monomial 9 (43 : ZMod 613) +
  monomial 10 (390 : ZMod 613) +
  monomial 11 (285 : ZMod 613)

/-- S2540T1^7 reduced modulo S2540F -/
def S2540D7 : (ZMod 613)[X] :=
  monomial 0 (301 : ZMod 613) +
  monomial 1 (439 : ZMod 613) +
  monomial 2 (169 : ZMod 613) +
  monomial 3 (418 : ZMod 613) +
  monomial 4 (79 : ZMod 613) +
  monomial 5 (221 : ZMod 613) +
  monomial 6 (37 : ZMod 613) +
  monomial 7 (536 : ZMod 613) +
  monomial 8 (202 : ZMod 613) +
  monomial 9 (229 : ZMod 613) +
  monomial 10 (432 : ZMod 613) +
  monomial 11 (222 : ZMod 613)

/-- S2540T1^8 reduced modulo S2540F -/
def S2540D8 : (ZMod 613)[X] :=
  monomial 0 (494 : ZMod 613) +
  monomial 1 (231 : ZMod 613) +
  monomial 2 (603 : ZMod 613) +
  monomial 3 (161 : ZMod 613) +
  monomial 4 (559 : ZMod 613) +
  monomial 5 (606 : ZMod 613) +
  monomial 6 (297 : ZMod 613) +
  monomial 7 (145 : ZMod 613) +
  monomial 8 (365 : ZMod 613) +
  monomial 9 (38 : ZMod 613) +
  monomial 10 (81 : ZMod 613) +
  monomial 11 (493 : ZMod 613)

/-- S2540T1^9 reduced modulo S2540F -/
def S2540D9 : (ZMod 613)[X] :=
  monomial 0 (501 : ZMod 613) +
  monomial 1 (568 : ZMod 613) +
  monomial 2 (72 : ZMod 613) +
  monomial 3 (454 : ZMod 613) +
  monomial 4 (440 : ZMod 613) +
  monomial 5 (83 : ZMod 613) +
  monomial 6 (260 : ZMod 613) +
  monomial 7 (328 : ZMod 613) +
  monomial 8 (218 : ZMod 613) +
  monomial 9 (531 : ZMod 613) +
  monomial 10 (133 : ZMod 613) +
  monomial 11 (372 : ZMod 613)

/-- S2540T1^10 reduced modulo S2540F -/
def S2540D10 : (ZMod 613)[X] :=
  monomial 0 (506 : ZMod 613) +
  monomial 1 (131 : ZMod 613) +
  monomial 2 (6 : ZMod 613) +
  monomial 3 (373 : ZMod 613) +
  monomial 4 (331 : ZMod 613) +
  monomial 5 (121 : ZMod 613) +
  monomial 6 (543 : ZMod 613) +
  monomial 7 (600 : ZMod 613) +
  monomial 8 (425 : ZMod 613) +
  monomial 9 (541 : ZMod 613) +
  monomial 10 (574 : ZMod 613) +
  monomial 11 (384 : ZMod 613)

/-- S2540T1^11 reduced modulo S2540F -/
def S2540D11 : (ZMod 613)[X] :=
  monomial 0 (118 : ZMod 613) +
  monomial 1 (192 : ZMod 613) +
  monomial 2 (424 : ZMod 613) +
  monomial 3 (25 : ZMod 613) +
  monomial 4 (368 : ZMod 613) +
  monomial 5 (65 : ZMod 613) +
  monomial 6 (398 : ZMod 613) +
  monomial 7 (364 : ZMod 613) +
  monomial 8 (214 : ZMod 613) +
  monomial 9 (222 : ZMod 613) +
  monomial 10 (540 : ZMod 613) +
  monomial 11 (453 : ZMod 613)

/-- cofactor of the S2540D2 certificate -/
def S2540E2 : (ZMod 613)[X] :=
  monomial 0 (526 : ZMod 613) +
  monomial 1 (242 : ZMod 613) +
  monomial 2 (377 : ZMod 613) +
  monomial 3 (207 : ZMod 613) +
  monomial 4 (399 : ZMod 613) +
  monomial 5 (197 : ZMod 613) +
  monomial 6 (69 : ZMod 613) +
  monomial 7 (246 : ZMod 613) +
  monomial 8 (96 : ZMod 613) +
  monomial 9 (390 : ZMod 613) +
  monomial 10 (124 : ZMod 613)

/-- cofactor of the S2540D3 certificate -/
def S2540E3 : (ZMod 613)[X] :=
  monomial 0 (341 : ZMod 613) +
  monomial 1 (29 : ZMod 613) +
  monomial 2 (86 : ZMod 613) +
  monomial 3 (22 : ZMod 613) +
  monomial 4 (188 : ZMod 613) +
  monomial 5 (495 : ZMod 613) +
  monomial 6 (6 : ZMod 613) +
  monomial 8 (261 : ZMod 613) +
  monomial 9 (290 : ZMod 613) +
  monomial 10 (150 : ZMod 613)

/-- cofactor of the S2540D4 certificate -/
def S2540E4 : (ZMod 613)[X] :=
  monomial 0 (268 : ZMod 613) +
  monomial 1 (508 : ZMod 613) +
  monomial 2 (458 : ZMod 613) +
  monomial 3 (239 : ZMod 613) +
  monomial 4 (64 : ZMod 613) +
  monomial 5 (83 : ZMod 613) +
  monomial 6 (398 : ZMod 613) +
  monomial 7 (238 : ZMod 613) +
  monomial 8 (450 : ZMod 613) +
  monomial 9 (605 : ZMod 613) +
  monomial 10 (568 : ZMod 613)

/-- cofactor of the S2540D5 certificate -/
def S2540E5 : (ZMod 613)[X] :=
  monomial 0 (466 : ZMod 613) +
  monomial 1 (196 : ZMod 613) +
  monomial 2 (448 : ZMod 613) +
  monomial 3 (229 : ZMod 613) +
  monomial 4 (175 : ZMod 613) +
  monomial 5 (457 : ZMod 613) +
  monomial 6 (495 : ZMod 613) +
  monomial 7 (3 : ZMod 613) +
  monomial 8 (294 : ZMod 613) +
  monomial 9 (472 : ZMod 613) +
  monomial 10 (126 : ZMod 613)

/-- cofactor of the S2540D6 certificate -/
def S2540E6 : (ZMod 613)[X] :=
  monomial 0 (322 : ZMod 613) +
  monomial 1 (283 : ZMod 613) +
  monomial 2 (373 : ZMod 613) +
  monomial 3 (165 : ZMod 613) +
  monomial 4 (212 : ZMod 613) +
  monomial 5 (211 : ZMod 613) +
  monomial 6 (448 : ZMod 613) +
  monomial 7 (374 : ZMod 613) +
  monomial 8 (228 : ZMod 613) +
  monomial 9 (216 : ZMod 613) +
  monomial 10 (600 : ZMod 613)

/-- cofactor of the S2540D7 certificate -/
def S2540E7 : (ZMod 613)[X] :=
  monomial 0 (233 : ZMod 613) +
  monomial 1 (276 : ZMod 613) +
  monomial 2 (215 : ZMod 613) +
  monomial 3 (526 : ZMod 613) +
  monomial 4 (69 : ZMod 613) +
  monomial 5 (80 : ZMod 613) +
  monomial 6 (3 : ZMod 613) +
  monomial 7 (495 : ZMod 613) +
  monomial 8 (161 : ZMod 613) +
  monomial 9 (266 : ZMod 613) +
  monomial 10 (175 : ZMod 613)

/-- cofactor of the S2540D8 certificate -/
def S2540E8 : (ZMod 613)[X] :=
  monomial 0 (404 : ZMod 613) +
  monomial 1 (112 : ZMod 613) +
  monomial 2 (344 : ZMod 613) +
  monomial 3 (225 : ZMod 613) +
  monomial 4 (35 : ZMod 613) +
  monomial 5 (271 : ZMod 613) +
  monomial 6 (234 : ZMod 613) +
  monomial 7 (271 : ZMod 613) +
  monomial 8 (371 : ZMod 613) +
  monomial 9 (326 : ZMod 613) +
  monomial 10 (588 : ZMod 613)

/-- cofactor of the S2540D9 certificate -/
def S2540E9 : (ZMod 613)[X] :=
  monomial 0 (131 : ZMod 613) +
  monomial 1 (567 : ZMod 613) +
  monomial 2 (533 : ZMod 613) +
  monomial 3 (454 : ZMod 613) +
  monomial 4 (290 : ZMod 613) +
  monomial 5 (420 : ZMod 613) +
  monomial 6 (87 : ZMod 613) +
  monomial 7 (354 : ZMod 613) +
  monomial 8 (68 : ZMod 613) +
  monomial 9 (98 : ZMod 613) +
  monomial 10 (378 : ZMod 613)

/-- cofactor of the S2540D10 certificate -/
def S2540E10 : (ZMod 613)[X] :=
  monomial 0 (338 : ZMod 613) +
  monomial 1 (589 : ZMod 613) +
  monomial 2 (280 : ZMod 613) +
  monomial 3 (256 : ZMod 613) +
  monomial 4 (526 : ZMod 613) +
  monomial 5 (362 : ZMod 613) +
  monomial 6 (139 : ZMod 613) +
  monomial 7 (576 : ZMod 613) +
  monomial 8 (228 : ZMod 613) +
  monomial 9 (359 : ZMod 613) +
  monomial 10 (422 : ZMod 613)

/-- cofactor of the S2540D11 certificate -/
def S2540E11 : (ZMod 613)[X] :=
  monomial 0 (96 : ZMod 613) +
  monomial 1 (155 : ZMod 613) +
  monomial 2 (294 : ZMod 613) +
  monomial 3 (345 : ZMod 613) +
  monomial 4 (595 : ZMod 613) +
  monomial 5 (368 : ZMod 613) +
  monomial 6 (330 : ZMod 613) +
  monomial 7 (38 : ZMod 613) +
  monomial 8 (455 : ZMod 613) +
  monomial 9 (41 : ZMod 613) +
  monomial 10 (139 : ZMod 613)

/-- X^(613^2) reduced modulo S2540F -/
def S2540T2 : (ZMod 613)[X] :=
  monomial 0 (355 : ZMod 613) +
  monomial 1 (93 : ZMod 613) +
  monomial 2 (539 : ZMod 613) +
  monomial 3 (217 : ZMod 613) +
  monomial 4 (396 : ZMod 613) +
  monomial 5 (278 : ZMod 613) +
  monomial 6 (226 : ZMod 613) +
  monomial 7 (130 : ZMod 613) +
  monomial 8 (271 : ZMod 613) +
  monomial 9 (126 : ZMod 613) +
  monomial 10 (43 : ZMod 613) +
  monomial 11 (398 : ZMod 613)

/-- X^(613^3) reduced modulo S2540F -/
def S2540T3 : (ZMod 613)[X] :=
  monomial 0 (299 : ZMod 613) +
  monomial 1 (602 : ZMod 613) +
  monomial 2 (530 : ZMod 613) +
  monomial 3 (47 : ZMod 613) +
  monomial 4 (332 : ZMod 613) +
  monomial 5 (190 : ZMod 613) +
  monomial 6 (121 : ZMod 613) +
  monomial 7 (293 : ZMod 613) +
  monomial 8 (268 : ZMod 613) +
  monomial 9 (391 : ZMod 613) +
  monomial 10 (329 : ZMod 613) +
  monomial 11 (375 : ZMod 613)

/-- X^(613^4) reduced modulo S2540F -/
def S2540T4 : (ZMod 613)[X] :=
  monomial 0 (304 : ZMod 613) +
  monomial 1 (381 : ZMod 613) +
  monomial 2 (485 : ZMod 613) +
  monomial 3 (30 : ZMod 613) +
  monomial 4 (70 : ZMod 613) +
  monomial 5 (493 : ZMod 613) +
  monomial 6 (560 : ZMod 613) +
  monomial 7 (423 : ZMod 613) +
  monomial 8 (252 : ZMod 613) +
  monomial 9 (575 : ZMod 613) +
  monomial 10 (186 : ZMod 613) +
  monomial 11 (15 : ZMod 613)

/-- X^(613^5) reduced modulo S2540F -/
def S2540T5 : (ZMod 613)[X] :=
  monomial 0 (110 : ZMod 613) +
  monomial 1 (342 : ZMod 613) +
  monomial 2 (437 : ZMod 613) +
  monomial 3 (166 : ZMod 613) +
  monomial 4 (448 : ZMod 613) +
  monomial 5 (312 : ZMod 613) +
  monomial 6 (99 : ZMod 613) +
  monomial 7 (53 : ZMod 613) +
  monomial 8 (125 : ZMod 613) +
  monomial 9 (334 : ZMod 613) +
  monomial 10 (132 : ZMod 613) +
  monomial 11 (576 : ZMod 613)

/-- X^(613^6) reduced modulo S2540F -/
def S2540T6 : (ZMod 613)[X] :=
  monomial 0 (449 : ZMod 613) +
  monomial 1 (608 : ZMod 613) +
  monomial 2 (97 : ZMod 613) +
  monomial 3 (88 : ZMod 613) +
  monomial 4 (311 : ZMod 613) +
  monomial 5 (248 : ZMod 613) +
  monomial 6 (430 : ZMod 613) +
  monomial 7 (477 : ZMod 613) +
  monomial 8 (162 : ZMod 613) +
  monomial 9 (280 : ZMod 613) +
  monomial 10 (259 : ZMod 613) +
  monomial 11 (580 : ZMod 613)

/-- X^(613^7) reduced modulo S2540F -/
def S2540T7 : (ZMod 613)[X] :=
  monomial 0 (594 : ZMod 613) +
  monomial 1 (447 : ZMod 613) +
  monomial 2 (417 : ZMod 613) +
  monomial 3 (577 : ZMod 613) +
  monomial 4 (563 : ZMod 613) +
  monomial 5 (236 : ZMod 613) +
  monomial 6 (103 : ZMod 613) +
  monomial 7 (378 : ZMod 613) +
  monomial 8 (126 : ZMod 613) +
  monomial 9 (427 : ZMod 613) +
  monomial 10 (242 : ZMod 613) +
  monomial 11 (412 : ZMod 613)

/-- X^(613^8) reduced modulo S2540F -/
def S2540T8 : (ZMod 613)[X] :=
  monomial 0 (406 : ZMod 613) +
  monomial 1 (611 : ZMod 613) +
  monomial 2 (186 : ZMod 613) +
  monomial 3 (143 : ZMod 613) +
  monomial 4 (554 : ZMod 613) +
  monomial 5 (117 : ZMod 613) +
  monomial 6 (286 : ZMod 613) +
  monomial 7 (87 : ZMod 613) +
  monomial 8 (526 : ZMod 613) +
  monomial 9 (402 : ZMod 613) +
  monomial 10 (495 : ZMod 613) +
  monomial 11 (180 : ZMod 613)

/-- X^(613^9) reduced modulo S2540F -/
def S2540T9 : (ZMod 613)[X] :=
  monomial 0 (533 : ZMod 613) +
  monomial 1 (297 : ZMod 613) +
  monomial 2 (483 : ZMod 613) +
  monomial 3 (536 : ZMod 613) +
  monomial 4 (11 : ZMod 613) +
  monomial 5 (273 : ZMod 613) +
  monomial 6 (352 : ZMod 613) +
  monomial 7 (303 : ZMod 613) +
  monomial 8 (338 : ZMod 613) +
  monomial 9 (64 : ZMod 613) +
  monomial 10 (403 : ZMod 613) +
  monomial 11 (32 : ZMod 613)

/-- X^(613^10) reduced modulo S2540F -/
def S2540T10 : (ZMod 613)[X] :=
  monomial 0 (14 : ZMod 613) +
  monomial 1 (405 : ZMod 613) +
  monomial 2 (548 : ZMod 613) +
  monomial 3 (441 : ZMod 613) +
  monomial 4 (289 : ZMod 613) +
  monomial 5 (364 : ZMod 613) +
  monomial 6 (234 : ZMod 613) +
  monomial 7 (186 : ZMod 613) +
  monomial 8 (463 : ZMod 613) +
  monomial 9 (151 : ZMod 613) +
  monomial 10 (232 : ZMod 613) +
  monomial 11 (49 : ZMod 613)

/-- X^(613^11) reduced modulo S2540F -/
def S2540T11 : (ZMod 613)[X] :=
  monomial 0 (154 : ZMod 613) +
  monomial 1 (344 : ZMod 613) +
  monomial 2 (39 : ZMod 613) +
  monomial 3 (512 : ZMod 613) +
  monomial 4 (174 : ZMod 613) +
  monomial 5 (275 : ZMod 613) +
  monomial 6 (34 : ZMod 613) +
  monomial 7 (168 : ZMod 613) +
  monomial 8 (102 : ZMod 613) +
  monomial 9 (27 : ZMod 613) +
  monomial 10 (302 : ZMod 613) +
  monomial 11 (176 : ZMod 613)

/-- X^(613^12) = X reduced modulo S2540F. -/
def S2540T12 : (ZMod 613)[X] := X

/-- The Frobenius table i |-> S2540T1^i mod S2540F. -/
def S2540Dfun : ℕ → (ZMod 613)[X]
  | 0 => S2540D0
  | 1 => S2540D1
  | 2 => S2540D2
  | 3 => S2540D3
  | 4 => S2540D4
  | 5 => S2540D5
  | 6 => S2540D6
  | 7 => S2540D7
  | 8 => S2540D8
  | 9 => S2540D9
  | 10 => S2540D10
  | 11 => S2540D11
  | _ => 0

/-- Bezout coefficient for gcd S2540F (S2540T4 - X) -/
def S2540P4 : (ZMod 613)[X] :=
  monomial 0 (525 : ZMod 613) +
  monomial 1 (119 : ZMod 613) +
  monomial 2 (468 : ZMod 613) +
  monomial 3 (127 : ZMod 613) +
  monomial 4 (142 : ZMod 613) +
  monomial 5 (365 : ZMod 613) +
  monomial 6 (43 : ZMod 613) +
  monomial 7 (557 : ZMod 613) +
  monomial 8 (460 : ZMod 613) +
  monomial 9 (554 : ZMod 613) +
  monomial 10 (566 : ZMod 613)

/-- Bezout coefficient for gcd S2540F (S2540T4 - X) -/
def S2540Q4 : (ZMod 613)[X] :=
  monomial 0 (594 : ZMod 613) +
  monomial 1 (315 : ZMod 613) +
  monomial 2 (228 : ZMod 613) +
  monomial 3 (152 : ZMod 613) +
  monomial 4 (129 : ZMod 613) +
  monomial 5 (272 : ZMod 613) +
  monomial 6 (169 : ZMod 613) +
  monomial 7 (346 : ZMod 613) +
  monomial 8 (108 : ZMod 613) +
  monomial 9 (47 : ZMod 613) +
  monomial 10 (366 : ZMod 613) +
  monomial 11 (190 : ZMod 613)

/-- Bezout coefficient for gcd S2540F (S2540T6 - X) -/
def S2540P6 : (ZMod 613)[X] :=
  monomial 0 (608 : ZMod 613) +
  monomial 1 (63 : ZMod 613) +
  monomial 2 (122 : ZMod 613) +
  monomial 3 (178 : ZMod 613) +
  monomial 4 (459 : ZMod 613) +
  monomial 5 (562 : ZMod 613) +
  monomial 6 (508 : ZMod 613) +
  monomial 7 (488 : ZMod 613) +
  monomial 8 (321 : ZMod 613) +
  monomial 9 (327 : ZMod 613) +
  monomial 10 (276 : ZMod 613)

/-- Bezout coefficient for gcd S2540F (S2540T6 - X) -/
def S2540Q6 : (ZMod 613)[X] :=
  monomial 0 (92 : ZMod 613) +
  monomial 1 (556 : ZMod 613) +
  monomial 2 (445 : ZMod 613) +
  monomial 3 (235 : ZMod 613) +
  monomial 4 (564 : ZMod 613) +
  monomial 5 (280 : ZMod 613) +
  monomial 6 (419 : ZMod 613) +
  monomial 7 (203 : ZMod 613) +
  monomial 8 (226 : ZMod 613) +
  monomial 9 (477 : ZMod 613) +
  monomial 10 (460 : ZMod 613) +
  monomial 11 (487 : ZMod 613)
/-! ## 5. The reduction certificates -/
/-- X^16 - S2540A16 = F * S2540S16. -/
lemma S2540cert16 : (X : (ZMod 613)[X]) ^ 16 - S2540A16 = S2540F * S2540S16 := by
  ext k
  by_cases hk : k ≤ 16
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [S2540F, S2540A16, S2540S16, coeff_add, coeff_sub, coeff_monomial, coeff_X_pow, coeff_X,
         coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char
       try decide)
  have hL : ((X : (ZMod 613)[X]) ^ 16 - S2540A16).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := (X : (ZMod 613)[X]) ^ 16 - S2540A16)
    have hdeg : ((X : (ZMod 613)[X]) ^ 16 - S2540A16).natDegree < 17 := by
      simp only [S2540F, S2540A16, S2540S16]
      compute_degree!
    omega
  have hR : (S2540F * S2540S16).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540F * S2540S16)
    have hdeg : (S2540F * S2540S16).natDegree < 17 := by
      simp only [S2540F, S2540A16, S2540S16]
      compute_degree!
    omega
  rw [hL, hR]

/-- Certificate S2540A16 * S2540A16 - S2540A32 = F * S2540S32. -/
lemma S2540cert32 : S2540A16 * S2540A16 - S2540A32 = S2540F * S2540S32 := by
  ext k
  by_cases hk : k ≤ 22
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [S2540F, S2540A16, S2540A32, S2540S32, coeff_add, coeff_sub, coeff_monomial, coeff_X_pow, coeff_X,
         coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char
       try decide)
  have hL : (S2540A16 * S2540A16 - S2540A32).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540A16 * S2540A16 - S2540A32)
    have hdeg : (S2540A16 * S2540A16 - S2540A32).natDegree < 23 := by
      simp only [S2540F, S2540A16, S2540A32, S2540S32]
      compute_degree!
    omega
  have hR : (S2540F * S2540S32).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540F * S2540S32)
    have hdeg : (S2540F * S2540S32).natDegree < 23 := by
      simp only [S2540F, S2540A16, S2540A32, S2540S32]
      compute_degree!
    omega
  rw [hL, hR]

/-- Certificate S2540A32 * S2540A32 - S2540A64 = F * S2540S64. -/
lemma S2540cert64 : S2540A32 * S2540A32 - S2540A64 = S2540F * S2540S64 := by
  ext k
  by_cases hk : k ≤ 22
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [S2540F, S2540A32, S2540A64, S2540S64, coeff_add, coeff_sub, coeff_monomial, coeff_X_pow, coeff_X,
         coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char
       try decide)
  have hL : (S2540A32 * S2540A32 - S2540A64).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540A32 * S2540A32 - S2540A64)
    have hdeg : (S2540A32 * S2540A32 - S2540A64).natDegree < 23 := by
      simp only [S2540F, S2540A32, S2540A64, S2540S64]
      compute_degree!
    omega
  have hR : (S2540F * S2540S64).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540F * S2540S64)
    have hdeg : (S2540F * S2540S64).natDegree < 23 := by
      simp only [S2540F, S2540A32, S2540A64, S2540S64]
      compute_degree!
    omega
  rw [hL, hR]

/-- Certificate S2540A64 * S2540A64 - S2540A128 = F * S2540S128. -/
lemma S2540cert128 : S2540A64 * S2540A64 - S2540A128 = S2540F * S2540S128 := by
  ext k
  by_cases hk : k ≤ 22
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [S2540F, S2540A64, S2540A128, S2540S128, coeff_add, coeff_sub, coeff_monomial, coeff_X_pow, coeff_X,
         coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char
       try decide)
  have hL : (S2540A64 * S2540A64 - S2540A128).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540A64 * S2540A64 - S2540A128)
    have hdeg : (S2540A64 * S2540A64 - S2540A128).natDegree < 23 := by
      simp only [S2540F, S2540A64, S2540A128, S2540S128]
      compute_degree!
    omega
  have hR : (S2540F * S2540S128).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540F * S2540S128)
    have hdeg : (S2540F * S2540S128).natDegree < 23 := by
      simp only [S2540F, S2540A64, S2540A128, S2540S128]
      compute_degree!
    omega
  rw [hL, hR]

/-- Certificate S2540A128 * S2540A128 - S2540A256 = F * S2540S256. -/
lemma S2540cert256 : S2540A128 * S2540A128 - S2540A256 = S2540F * S2540S256 := by
  ext k
  by_cases hk : k ≤ 22
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [S2540F, S2540A128, S2540A256, S2540S256, coeff_add, coeff_sub, coeff_monomial, coeff_X_pow, coeff_X,
         coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char
       try decide)
  have hL : (S2540A128 * S2540A128 - S2540A256).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540A128 * S2540A128 - S2540A256)
    have hdeg : (S2540A128 * S2540A128 - S2540A256).natDegree < 23 := by
      simp only [S2540F, S2540A128, S2540A256, S2540S256]
      compute_degree!
    omega
  have hR : (S2540F * S2540S256).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540F * S2540S256)
    have hdeg : (S2540F * S2540S256).natDegree < 23 := by
      simp only [S2540F, S2540A128, S2540A256, S2540S256]
      compute_degree!
    omega
  rw [hL, hR]

/-- Certificate S2540A256 * S2540A256 - S2540A512 = F * S2540S512. -/
lemma S2540cert512 : S2540A256 * S2540A256 - S2540A512 = S2540F * S2540S512 := by
  ext k
  by_cases hk : k ≤ 22
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [S2540F, S2540A256, S2540A512, S2540S512, coeff_add, coeff_sub, coeff_monomial, coeff_X_pow, coeff_X,
         coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char
       try decide)
  have hL : (S2540A256 * S2540A256 - S2540A512).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540A256 * S2540A256 - S2540A512)
    have hdeg : (S2540A256 * S2540A256 - S2540A512).natDegree < 23 := by
      simp only [S2540F, S2540A256, S2540A512, S2540S512]
      compute_degree!
    omega
  have hR : (S2540F * S2540S512).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540F * S2540S512)
    have hdeg : (S2540F * S2540S512).natDegree < 23 := by
      simp only [S2540F, S2540A256, S2540A512, S2540S512]
      compute_degree!
    omega
  rw [hL, hR]

/-- Certificate S2540A512 * S2540A64 - S2540M1 = F * S2540SM1. -/
lemma S2540certM1 : S2540A512 * S2540A64 - S2540M1 = S2540F * S2540SM1 := by
  ext k
  by_cases hk : k ≤ 22
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [S2540F, S2540A512, S2540A64, S2540M1, S2540SM1, coeff_add, coeff_sub, coeff_monomial, coeff_X_pow, coeff_X,
         coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char
       try decide)
  have hL : (S2540A512 * S2540A64 - S2540M1).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540A512 * S2540A64 - S2540M1)
    have hdeg : (S2540A512 * S2540A64 - S2540M1).natDegree < 23 := by
      simp only [S2540F, S2540A512, S2540A64, S2540M1, S2540SM1]
      compute_degree!
    omega
  have hR : (S2540F * S2540SM1).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540F * S2540SM1)
    have hdeg : (S2540F * S2540SM1).natDegree < 23 := by
      simp only [S2540F, S2540A512, S2540A64, S2540M1, S2540SM1]
      compute_degree!
    omega
  rw [hL, hR]

/-- Certificate S2540M1 * S2540A32 - S2540M2 = F * S2540SM2. -/
lemma S2540certM2 : S2540M1 * S2540A32 - S2540M2 = S2540F * S2540SM2 := by
  ext k
  by_cases hk : k ≤ 22
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [S2540F, S2540M1, S2540A32, S2540M2, S2540SM2, coeff_add, coeff_sub, coeff_monomial, coeff_X_pow, coeff_X,
         coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char
       try decide)
  have hL : (S2540M1 * S2540A32 - S2540M2).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540M1 * S2540A32 - S2540M2)
    have hdeg : (S2540M1 * S2540A32 - S2540M2).natDegree < 23 := by
      simp only [S2540F, S2540M1, S2540A32, S2540M2, S2540SM2]
      compute_degree!
    omega
  have hR : (S2540F * S2540SM2).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540F * S2540SM2)
    have hdeg : (S2540F * S2540SM2).natDegree < 23 := by
      simp only [S2540F, S2540M1, S2540A32, S2540M2, S2540SM2]
      compute_degree!
    omega
  rw [hL, hR]

/-- Certificate S2540M2 * S2540A4 - S2540M3 = F * S2540SM3. -/
lemma S2540certM3 : S2540M2 * S2540A4 - S2540M3 = S2540F * S2540SM3 := by
  ext k
  by_cases hk : k ≤ 15
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [S2540F, S2540M2, S2540A4, S2540M3, S2540SM3, coeff_add, coeff_sub, coeff_monomial, coeff_X_pow, coeff_X,
         coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char
       try decide)
  have hL : (S2540M2 * S2540A4 - S2540M3).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540M2 * S2540A4 - S2540M3)
    have hdeg : (S2540M2 * S2540A4 - S2540M3).natDegree < 16 := by
      simp only [S2540F, S2540M2, S2540A4, S2540M3, S2540SM3]
      compute_degree!
    omega
  have hR : (S2540F * S2540SM3).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540F * S2540SM3)
    have hdeg : (S2540F * S2540SM3).natDegree < 16 := by
      simp only [S2540F, S2540M2, S2540A4, S2540M3, S2540SM3]
      compute_degree!
    omega
  rw [hL, hR]

/-- Certificate S2540M3 * S2540A1 - S2540T1 = F * S2540ST1. -/
lemma S2540certT1 : S2540M3 * S2540A1 - S2540T1 = S2540F * S2540ST1 := by
  ext k
  by_cases hk : k ≤ 12
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [S2540F, S2540M3, S2540A1, S2540T1, S2540ST1, coeff_add, coeff_sub, coeff_monomial, coeff_X_pow, coeff_X,
         coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char
       try decide)
  have hL : (S2540M3 * S2540A1 - S2540T1).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540M3 * S2540A1 - S2540T1)
    have hdeg : (S2540M3 * S2540A1 - S2540T1).natDegree < 13 := by
      simp only [S2540F, S2540M3, S2540A1, S2540T1, S2540ST1]
      compute_degree!
    omega
  have hR : (S2540F * S2540ST1).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540F * S2540ST1)
    have hdeg : (S2540F * S2540ST1).natDegree < 13 := by
      simp only [S2540F, S2540M3, S2540A1, S2540T1, S2540ST1]
      compute_degree!
    omega
  rw [hL, hR]

/-- Certificate S2540D1 * S2540T1 - S2540D2 = F * S2540E2. -/
lemma S2540certD2 : S2540D1 * S2540T1 - S2540D2 = S2540F * S2540E2 := by
  ext k
  by_cases hk : k ≤ 22
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [S2540F, S2540D1, S2540T1, S2540D2, S2540E2, coeff_add, coeff_sub, coeff_monomial, coeff_X_pow, coeff_X,
         coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char
       try decide)
  have hL : (S2540D1 * S2540T1 - S2540D2).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540D1 * S2540T1 - S2540D2)
    have hdeg : (S2540D1 * S2540T1 - S2540D2).natDegree < 23 := by
      simp only [S2540F, S2540D1, S2540T1, S2540D2, S2540E2]
      compute_degree!
    omega
  have hR : (S2540F * S2540E2).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540F * S2540E2)
    have hdeg : (S2540F * S2540E2).natDegree < 23 := by
      simp only [S2540F, S2540D1, S2540T1, S2540D2, S2540E2]
      compute_degree!
    omega
  rw [hL, hR]

/-- Certificate S2540D2 * S2540T1 - S2540D3 = F * S2540E3. -/
lemma S2540certD3 : S2540D2 * S2540T1 - S2540D3 = S2540F * S2540E3 := by
  ext k
  by_cases hk : k ≤ 22
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [S2540F, S2540D2, S2540T1, S2540D3, S2540E3, coeff_add, coeff_sub, coeff_monomial, coeff_X_pow, coeff_X,
         coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char
       try decide)
  have hL : (S2540D2 * S2540T1 - S2540D3).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540D2 * S2540T1 - S2540D3)
    have hdeg : (S2540D2 * S2540T1 - S2540D3).natDegree < 23 := by
      simp only [S2540F, S2540D2, S2540T1, S2540D3, S2540E3]
      compute_degree!
    omega
  have hR : (S2540F * S2540E3).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540F * S2540E3)
    have hdeg : (S2540F * S2540E3).natDegree < 23 := by
      simp only [S2540F, S2540D2, S2540T1, S2540D3, S2540E3]
      compute_degree!
    omega
  rw [hL, hR]

/-- Certificate S2540D3 * S2540T1 - S2540D4 = F * S2540E4. -/
lemma S2540certD4 : S2540D3 * S2540T1 - S2540D4 = S2540F * S2540E4 := by
  ext k
  by_cases hk : k ≤ 22
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [S2540F, S2540D3, S2540T1, S2540D4, S2540E4, coeff_add, coeff_sub, coeff_monomial, coeff_X_pow, coeff_X,
         coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char
       try decide)
  have hL : (S2540D3 * S2540T1 - S2540D4).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540D3 * S2540T1 - S2540D4)
    have hdeg : (S2540D3 * S2540T1 - S2540D4).natDegree < 23 := by
      simp only [S2540F, S2540D3, S2540T1, S2540D4, S2540E4]
      compute_degree!
    omega
  have hR : (S2540F * S2540E4).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540F * S2540E4)
    have hdeg : (S2540F * S2540E4).natDegree < 23 := by
      simp only [S2540F, S2540D3, S2540T1, S2540D4, S2540E4]
      compute_degree!
    omega
  rw [hL, hR]

/-- Certificate S2540D4 * S2540T1 - S2540D5 = F * S2540E5. -/
lemma S2540certD5 : S2540D4 * S2540T1 - S2540D5 = S2540F * S2540E5 := by
  ext k
  by_cases hk : k ≤ 22
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [S2540F, S2540D4, S2540T1, S2540D5, S2540E5, coeff_add, coeff_sub, coeff_monomial, coeff_X_pow, coeff_X,
         coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char
       try decide)
  have hL : (S2540D4 * S2540T1 - S2540D5).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540D4 * S2540T1 - S2540D5)
    have hdeg : (S2540D4 * S2540T1 - S2540D5).natDegree < 23 := by
      simp only [S2540F, S2540D4, S2540T1, S2540D5, S2540E5]
      compute_degree!
    omega
  have hR : (S2540F * S2540E5).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540F * S2540E5)
    have hdeg : (S2540F * S2540E5).natDegree < 23 := by
      simp only [S2540F, S2540D4, S2540T1, S2540D5, S2540E5]
      compute_degree!
    omega
  rw [hL, hR]

/-- Certificate S2540D5 * S2540T1 - S2540D6 = F * S2540E6. -/
lemma S2540certD6 : S2540D5 * S2540T1 - S2540D6 = S2540F * S2540E6 := by
  ext k
  by_cases hk : k ≤ 22
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [S2540F, S2540D5, S2540T1, S2540D6, S2540E6, coeff_add, coeff_sub, coeff_monomial, coeff_X_pow, coeff_X,
         coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char
       try decide)
  have hL : (S2540D5 * S2540T1 - S2540D6).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540D5 * S2540T1 - S2540D6)
    have hdeg : (S2540D5 * S2540T1 - S2540D6).natDegree < 23 := by
      simp only [S2540F, S2540D5, S2540T1, S2540D6, S2540E6]
      compute_degree!
    omega
  have hR : (S2540F * S2540E6).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540F * S2540E6)
    have hdeg : (S2540F * S2540E6).natDegree < 23 := by
      simp only [S2540F, S2540D5, S2540T1, S2540D6, S2540E6]
      compute_degree!
    omega
  rw [hL, hR]

/-- Certificate S2540D6 * S2540T1 - S2540D7 = F * S2540E7. -/
lemma S2540certD7 : S2540D6 * S2540T1 - S2540D7 = S2540F * S2540E7 := by
  ext k
  by_cases hk : k ≤ 22
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [S2540F, S2540D6, S2540T1, S2540D7, S2540E7, coeff_add, coeff_sub, coeff_monomial, coeff_X_pow, coeff_X,
         coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char
       try decide)
  have hL : (S2540D6 * S2540T1 - S2540D7).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540D6 * S2540T1 - S2540D7)
    have hdeg : (S2540D6 * S2540T1 - S2540D7).natDegree < 23 := by
      simp only [S2540F, S2540D6, S2540T1, S2540D7, S2540E7]
      compute_degree!
    omega
  have hR : (S2540F * S2540E7).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540F * S2540E7)
    have hdeg : (S2540F * S2540E7).natDegree < 23 := by
      simp only [S2540F, S2540D6, S2540T1, S2540D7, S2540E7]
      compute_degree!
    omega
  rw [hL, hR]

/-- Certificate S2540D7 * S2540T1 - S2540D8 = F * S2540E8. -/
lemma S2540certD8 : S2540D7 * S2540T1 - S2540D8 = S2540F * S2540E8 := by
  ext k
  by_cases hk : k ≤ 22
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [S2540F, S2540D7, S2540T1, S2540D8, S2540E8, coeff_add, coeff_sub, coeff_monomial, coeff_X_pow, coeff_X,
         coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char
       try decide)
  have hL : (S2540D7 * S2540T1 - S2540D8).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540D7 * S2540T1 - S2540D8)
    have hdeg : (S2540D7 * S2540T1 - S2540D8).natDegree < 23 := by
      simp only [S2540F, S2540D7, S2540T1, S2540D8, S2540E8]
      compute_degree!
    omega
  have hR : (S2540F * S2540E8).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540F * S2540E8)
    have hdeg : (S2540F * S2540E8).natDegree < 23 := by
      simp only [S2540F, S2540D7, S2540T1, S2540D8, S2540E8]
      compute_degree!
    omega
  rw [hL, hR]

/-- Certificate S2540D8 * S2540T1 - S2540D9 = F * S2540E9. -/
lemma S2540certD9 : S2540D8 * S2540T1 - S2540D9 = S2540F * S2540E9 := by
  ext k
  by_cases hk : k ≤ 22
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [S2540F, S2540D8, S2540T1, S2540D9, S2540E9, coeff_add, coeff_sub, coeff_monomial, coeff_X_pow, coeff_X,
         coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char
       try decide)
  have hL : (S2540D8 * S2540T1 - S2540D9).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540D8 * S2540T1 - S2540D9)
    have hdeg : (S2540D8 * S2540T1 - S2540D9).natDegree < 23 := by
      simp only [S2540F, S2540D8, S2540T1, S2540D9, S2540E9]
      compute_degree!
    omega
  have hR : (S2540F * S2540E9).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540F * S2540E9)
    have hdeg : (S2540F * S2540E9).natDegree < 23 := by
      simp only [S2540F, S2540D8, S2540T1, S2540D9, S2540E9]
      compute_degree!
    omega
  rw [hL, hR]

/-- Certificate S2540D9 * S2540T1 - S2540D10 = F * S2540E10. -/
lemma S2540certD10 : S2540D9 * S2540T1 - S2540D10 = S2540F * S2540E10 := by
  ext k
  by_cases hk : k ≤ 22
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [S2540F, S2540D9, S2540T1, S2540D10, S2540E10, coeff_add, coeff_sub, coeff_monomial, coeff_X_pow, coeff_X,
         coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char
       try decide)
  have hL : (S2540D9 * S2540T1 - S2540D10).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540D9 * S2540T1 - S2540D10)
    have hdeg : (S2540D9 * S2540T1 - S2540D10).natDegree < 23 := by
      simp only [S2540F, S2540D9, S2540T1, S2540D10, S2540E10]
      compute_degree!
    omega
  have hR : (S2540F * S2540E10).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540F * S2540E10)
    have hdeg : (S2540F * S2540E10).natDegree < 23 := by
      simp only [S2540F, S2540D9, S2540T1, S2540D10, S2540E10]
      compute_degree!
    omega
  rw [hL, hR]

/-- Certificate S2540D10 * S2540T1 - S2540D11 = F * S2540E11. -/
lemma S2540certD11 : S2540D10 * S2540T1 - S2540D11 = S2540F * S2540E11 := by
  ext k
  by_cases hk : k ≤ 22
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [S2540F, S2540D10, S2540T1, S2540D11, S2540E11, coeff_add, coeff_sub, coeff_monomial, coeff_X_pow, coeff_X,
         coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char
       try decide)
  have hL : (S2540D10 * S2540T1 - S2540D11).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540D10 * S2540T1 - S2540D11)
    have hdeg : (S2540D10 * S2540T1 - S2540D11).natDegree < 23 := by
      simp only [S2540F, S2540D10, S2540T1, S2540D11, S2540E11]
      compute_degree!
    omega
  have hR : (S2540F * S2540E11).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540F * S2540E11)
    have hdeg : (S2540F * S2540E11).natDegree < 23 := by
      simp only [S2540F, S2540D10, S2540T1, S2540D11, S2540E11]
      compute_degree!
    omega
  rw [hL, hR]

/-- Bezout certificate P4 * F + Q4 * (T4 - X) = 1. -/
lemma S2540certP4 : S2540P4 * S2540F + S2540Q4 * (S2540T4 - X) = (1 : (ZMod 613)[X]) := by
  ext k
  by_cases hk : k ≤ 22
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [S2540P4, S2540Q4, S2540F, S2540T4, coeff_add, coeff_sub, coeff_monomial, coeff_X_pow, coeff_X,
         coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char
       try decide)
  have hL : (S2540P4 * S2540F + S2540Q4 * (S2540T4 - X)).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540P4 * S2540F + S2540Q4 * (S2540T4 - X))
    have hdeg : (S2540P4 * S2540F + S2540Q4 * (S2540T4 - X)).natDegree < 23 := by
      simp only [S2540P4, S2540Q4, S2540F, S2540T4]
      compute_degree!
    omega
  have hR : ((1 : (ZMod 613)[X])).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := (1 : (ZMod 613)[X]))
    have hdeg : ((1 : (ZMod 613)[X])).natDegree < 23 := by
      norm_num
    omega
  rw [hL, hR]

/-- Bezout certificate P6 * F + Q6 * (T6 - X) = 1. -/
lemma S2540certP6 : S2540P6 * S2540F + S2540Q6 * (S2540T6 - X) = (1 : (ZMod 613)[X]) := by
  ext k
  by_cases hk : k ≤ 22
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [S2540P6, S2540Q6, S2540F, S2540T6, coeff_add, coeff_sub, coeff_monomial, coeff_X_pow, coeff_X,
         coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char
       try decide)
  have hL : (S2540P6 * S2540F + S2540Q6 * (S2540T6 - X)).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := S2540P6 * S2540F + S2540Q6 * (S2540T6 - X))
    have hdeg : (S2540P6 * S2540F + S2540Q6 * (S2540T6 - X)).natDegree < 23 := by
      simp only [S2540P6, S2540Q6, S2540F, S2540T6]
      compute_degree!
    omega
  have hR : ((1 : (ZMod 613)[X])).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := (1 : (ZMod 613)[X]))
    have hdeg : ((1 : (ZMod 613)[X])).natDegree < 23 := by
      norm_num
    omega
  rw [hL, hR]

/-! ## 6. The divisibility chain for X^613 -/

lemma S2540h4 : S2540F ∣ (X : (ZMod 613)[X]) ^ 4 - S2540A4 := by
  simp [S2540A4]

lemma S2540h1 : S2540F ∣ (X : (ZMod 613)[X]) ^ 1 - S2540A1 := by
  simp [S2540A1]

lemma S2540h16 : S2540F ∣ (X : (ZMod 613)[X]) ^ 16 - S2540A16 := by
  rw [S2540cert16]
  exact dvd_mul_right _ _
lemma S2540h32 : S2540F ∣ (X : (ZMod 613)[X]) ^ 32 - S2540A32 := by
  have h := S2540dvd_pow_add (a := 16) (b := 16) S2540cert32 S2540h16 S2540h16
  rw [show 16 + 16 = 32 by norm_num] at h
  exact h

lemma S2540h64 : S2540F ∣ (X : (ZMod 613)[X]) ^ 64 - S2540A64 := by
  have h := S2540dvd_pow_add (a := 32) (b := 32) S2540cert64 S2540h32 S2540h32
  rw [show 32 + 32 = 64 by norm_num] at h
  exact h

lemma S2540h128 : S2540F ∣ (X : (ZMod 613)[X]) ^ 128 - S2540A128 := by
  have h := S2540dvd_pow_add (a := 64) (b := 64) S2540cert128 S2540h64 S2540h64
  rw [show 64 + 64 = 128 by norm_num] at h
  exact h

lemma S2540h256 : S2540F ∣ (X : (ZMod 613)[X]) ^ 256 - S2540A256 := by
  have h := S2540dvd_pow_add (a := 128) (b := 128) S2540cert256 S2540h128 S2540h128
  rw [show 128 + 128 = 256 by norm_num] at h
  exact h

lemma S2540h512 : S2540F ∣ (X : (ZMod 613)[X]) ^ 512 - S2540A512 := by
  have h := S2540dvd_pow_add (a := 256) (b := 256) S2540cert512 S2540h256 S2540h256
  rw [show 256 + 256 = 512 by norm_num] at h
  exact h

lemma S2540h576 : S2540F ∣ (X : (ZMod 613)[X]) ^ 576 - S2540M1 := by
  have h := S2540dvd_pow_add (a := 512) (b := 64) S2540certM1 S2540h512 S2540h64
  rw [show 512 + 64 = 576 by norm_num] at h
  exact h

lemma S2540h608 : S2540F ∣ (X : (ZMod 613)[X]) ^ 608 - S2540M2 := by
  have h := S2540dvd_pow_add (a := 576) (b := 32) S2540certM2 S2540h576 S2540h32
  rw [show 576 + 32 = 608 by norm_num] at h
  exact h

lemma S2540h612 : S2540F ∣ (X : (ZMod 613)[X]) ^ 612 - S2540M3 := by
  have h := S2540dvd_pow_add (a := 608) (b := 4) S2540certM3 S2540h608 S2540h4
  rw [show 608 + 4 = 612 by norm_num] at h
  exact h

lemma S2540h613 : S2540F ∣ (X : (ZMod 613)[X]) ^ 613 - S2540T1 := by
  have h := S2540dvd_pow_add (a := 612) (b := 1) S2540certT1 S2540h612 S2540h1
  rw [show 612 + 1 = 613 by norm_num] at h
  exact h

/-! ## 7. The power identities for the Frobenius table -/

lemma S2540D0_aeval : aeval S2540x S2540D0 = (aeval S2540x S2540T1) ^ 0 := by
  simp [S2540D0]

lemma S2540D1_aeval : aeval S2540x S2540D1 = (aeval S2540x S2540T1) ^ 1 := by
  simp [S2540D1]
lemma S2540D2_aeval : aeval S2540x S2540D2 = (aeval S2540x S2540T1) ^ 2 := by
  have h : aeval S2540x (S2540D1 * S2540T1 - S2540D2) = 0 := by
    rw [S2540certD2]
    simp only [map_mul, S2540aeval_F, zero_mul]
  have h2 : aeval S2540x (S2540D1 * S2540T1) - aeval S2540x S2540D2 = 0 := by
    simpa using h
  calc aeval S2540x S2540D2 = aeval S2540x (S2540D1 * S2540T1) :=
        (sub_eq_zero.mp h2).symm
    _ = aeval S2540x S2540D1 * aeval S2540x S2540T1 := by rw [map_mul]
    _ = (aeval S2540x S2540T1) ^ 1 * aeval S2540x S2540T1 := by
        rw [S2540D1_aeval]
    _ = (aeval S2540x S2540T1) ^ 2 := by ring

lemma S2540D3_aeval : aeval S2540x S2540D3 = (aeval S2540x S2540T1) ^ 3 := by
  have h : aeval S2540x (S2540D2 * S2540T1 - S2540D3) = 0 := by
    rw [S2540certD3]
    simp only [map_mul, S2540aeval_F, zero_mul]
  have h2 : aeval S2540x (S2540D2 * S2540T1) - aeval S2540x S2540D3 = 0 := by
    simpa using h
  calc aeval S2540x S2540D3 = aeval S2540x (S2540D2 * S2540T1) :=
        (sub_eq_zero.mp h2).symm
    _ = aeval S2540x S2540D2 * aeval S2540x S2540T1 := by rw [map_mul]
    _ = (aeval S2540x S2540T1) ^ 2 * aeval S2540x S2540T1 := by
        rw [S2540D2_aeval]
    _ = (aeval S2540x S2540T1) ^ 3 := by ring

lemma S2540D4_aeval : aeval S2540x S2540D4 = (aeval S2540x S2540T1) ^ 4 := by
  have h : aeval S2540x (S2540D3 * S2540T1 - S2540D4) = 0 := by
    rw [S2540certD4]
    simp only [map_mul, S2540aeval_F, zero_mul]
  have h2 : aeval S2540x (S2540D3 * S2540T1) - aeval S2540x S2540D4 = 0 := by
    simpa using h
  calc aeval S2540x S2540D4 = aeval S2540x (S2540D3 * S2540T1) :=
        (sub_eq_zero.mp h2).symm
    _ = aeval S2540x S2540D3 * aeval S2540x S2540T1 := by rw [map_mul]
    _ = (aeval S2540x S2540T1) ^ 3 * aeval S2540x S2540T1 := by
        rw [S2540D3_aeval]
    _ = (aeval S2540x S2540T1) ^ 4 := by ring

lemma S2540D5_aeval : aeval S2540x S2540D5 = (aeval S2540x S2540T1) ^ 5 := by
  have h : aeval S2540x (S2540D4 * S2540T1 - S2540D5) = 0 := by
    rw [S2540certD5]
    simp only [map_mul, S2540aeval_F, zero_mul]
  have h2 : aeval S2540x (S2540D4 * S2540T1) - aeval S2540x S2540D5 = 0 := by
    simpa using h
  calc aeval S2540x S2540D5 = aeval S2540x (S2540D4 * S2540T1) :=
        (sub_eq_zero.mp h2).symm
    _ = aeval S2540x S2540D4 * aeval S2540x S2540T1 := by rw [map_mul]
    _ = (aeval S2540x S2540T1) ^ 4 * aeval S2540x S2540T1 := by
        rw [S2540D4_aeval]
    _ = (aeval S2540x S2540T1) ^ 5 := by ring

lemma S2540D6_aeval : aeval S2540x S2540D6 = (aeval S2540x S2540T1) ^ 6 := by
  have h : aeval S2540x (S2540D5 * S2540T1 - S2540D6) = 0 := by
    rw [S2540certD6]
    simp only [map_mul, S2540aeval_F, zero_mul]
  have h2 : aeval S2540x (S2540D5 * S2540T1) - aeval S2540x S2540D6 = 0 := by
    simpa using h
  calc aeval S2540x S2540D6 = aeval S2540x (S2540D5 * S2540T1) :=
        (sub_eq_zero.mp h2).symm
    _ = aeval S2540x S2540D5 * aeval S2540x S2540T1 := by rw [map_mul]
    _ = (aeval S2540x S2540T1) ^ 5 * aeval S2540x S2540T1 := by
        rw [S2540D5_aeval]
    _ = (aeval S2540x S2540T1) ^ 6 := by ring

lemma S2540D7_aeval : aeval S2540x S2540D7 = (aeval S2540x S2540T1) ^ 7 := by
  have h : aeval S2540x (S2540D6 * S2540T1 - S2540D7) = 0 := by
    rw [S2540certD7]
    simp only [map_mul, S2540aeval_F, zero_mul]
  have h2 : aeval S2540x (S2540D6 * S2540T1) - aeval S2540x S2540D7 = 0 := by
    simpa using h
  calc aeval S2540x S2540D7 = aeval S2540x (S2540D6 * S2540T1) :=
        (sub_eq_zero.mp h2).symm
    _ = aeval S2540x S2540D6 * aeval S2540x S2540T1 := by rw [map_mul]
    _ = (aeval S2540x S2540T1) ^ 6 * aeval S2540x S2540T1 := by
        rw [S2540D6_aeval]
    _ = (aeval S2540x S2540T1) ^ 7 := by ring

lemma S2540D8_aeval : aeval S2540x S2540D8 = (aeval S2540x S2540T1) ^ 8 := by
  have h : aeval S2540x (S2540D7 * S2540T1 - S2540D8) = 0 := by
    rw [S2540certD8]
    simp only [map_mul, S2540aeval_F, zero_mul]
  have h2 : aeval S2540x (S2540D7 * S2540T1) - aeval S2540x S2540D8 = 0 := by
    simpa using h
  calc aeval S2540x S2540D8 = aeval S2540x (S2540D7 * S2540T1) :=
        (sub_eq_zero.mp h2).symm
    _ = aeval S2540x S2540D7 * aeval S2540x S2540T1 := by rw [map_mul]
    _ = (aeval S2540x S2540T1) ^ 7 * aeval S2540x S2540T1 := by
        rw [S2540D7_aeval]
    _ = (aeval S2540x S2540T1) ^ 8 := by ring

lemma S2540D9_aeval : aeval S2540x S2540D9 = (aeval S2540x S2540T1) ^ 9 := by
  have h : aeval S2540x (S2540D8 * S2540T1 - S2540D9) = 0 := by
    rw [S2540certD9]
    simp only [map_mul, S2540aeval_F, zero_mul]
  have h2 : aeval S2540x (S2540D8 * S2540T1) - aeval S2540x S2540D9 = 0 := by
    simpa using h
  calc aeval S2540x S2540D9 = aeval S2540x (S2540D8 * S2540T1) :=
        (sub_eq_zero.mp h2).symm
    _ = aeval S2540x S2540D8 * aeval S2540x S2540T1 := by rw [map_mul]
    _ = (aeval S2540x S2540T1) ^ 8 * aeval S2540x S2540T1 := by
        rw [S2540D8_aeval]
    _ = (aeval S2540x S2540T1) ^ 9 := by ring

lemma S2540D10_aeval : aeval S2540x S2540D10 = (aeval S2540x S2540T1) ^ 10 := by
  have h : aeval S2540x (S2540D9 * S2540T1 - S2540D10) = 0 := by
    rw [S2540certD10]
    simp only [map_mul, S2540aeval_F, zero_mul]
  have h2 : aeval S2540x (S2540D9 * S2540T1) - aeval S2540x S2540D10 = 0 := by
    simpa using h
  calc aeval S2540x S2540D10 = aeval S2540x (S2540D9 * S2540T1) :=
        (sub_eq_zero.mp h2).symm
    _ = aeval S2540x S2540D9 * aeval S2540x S2540T1 := by rw [map_mul]
    _ = (aeval S2540x S2540T1) ^ 9 * aeval S2540x S2540T1 := by
        rw [S2540D9_aeval]
    _ = (aeval S2540x S2540T1) ^ 10 := by ring

lemma S2540D11_aeval : aeval S2540x S2540D11 = (aeval S2540x S2540T1) ^ 11 := by
  have h : aeval S2540x (S2540D10 * S2540T1 - S2540D11) = 0 := by
    rw [S2540certD11]
    simp only [map_mul, S2540aeval_F, zero_mul]
  have h2 : aeval S2540x (S2540D10 * S2540T1) - aeval S2540x S2540D11 = 0 := by
    simpa using h
  calc aeval S2540x S2540D11 = aeval S2540x (S2540D10 * S2540T1) :=
        (sub_eq_zero.mp h2).symm
    _ = aeval S2540x S2540D10 * aeval S2540x S2540T1 := by rw [map_mul]
    _ = (aeval S2540x S2540T1) ^ 10 * aeval S2540x S2540T1 := by
        rw [S2540D10_aeval]
    _ = (aeval S2540x S2540T1) ^ 11 := by ring

lemma S2540D_aeval_all : ∀ i < 12, aeval S2540x (S2540Dfun i) = (aeval S2540x S2540T1) ^ i := by
  intro i hi
  interval_cases i
  · simpa [S2540Dfun] using S2540D0_aeval
  · simpa [S2540Dfun] using S2540D1_aeval
  · simpa [S2540Dfun] using S2540D2_aeval
  · simpa [S2540Dfun] using S2540D3_aeval
  · simpa [S2540Dfun] using S2540D4_aeval
  · simpa [S2540Dfun] using S2540D5_aeval
  · simpa [S2540Dfun] using S2540D6_aeval
  · simpa [S2540Dfun] using S2540D7_aeval
  · simpa [S2540Dfun] using S2540D8_aeval
  · simpa [S2540Dfun] using S2540D9_aeval
  · simpa [S2540Dfun] using S2540D10_aeval
  · simpa [S2540Dfun] using S2540D11_aeval

lemma S2540Dfun_deg (i : ℕ) (hi : i < 12) : (S2540Dfun i).natDegree ≤ 11 := by
  interval_cases i <;>
    (simp [S2540Dfun, S2540D0, S2540D1, S2540D2, S2540D3, S2540D4, S2540D5,
      S2540D6, S2540D7, S2540D8, S2540D9, S2540D10, S2540D11] <;> compute_degree!)

lemma S2540sum_deg (P : (ZMod 613)[X]) :
    (∑ i ∈ Finset.range 12, C (P.coeff i) * S2540Dfun i).natDegree ≤ 11 := by
  refine natDegree_sum_le_of_forall_le (fun i => C (P.coeff i) * S2540Dfun i) ?_
  intro i hi
  calc (C (P.coeff i) * S2540Dfun i).natDegree ≤ (S2540Dfun i).natDegree :=
        natDegree_C_mul_le _ _
    _ ≤ 11 := S2540Dfun_deg i (Finset.mem_range.mp hi)

/-! ## 8. The Frobenius iterates -/

lemma S2540T1deg : S2540T1.natDegree < 12 := by
  simp only [S2540T1]
  compute_degree!

lemma S2540T2deg : S2540T2.natDegree < 12 := by
  simp only [S2540T2]
  compute_degree!

lemma S2540T3deg : S2540T3.natDegree < 12 := by
  simp only [S2540T3]
  compute_degree!

lemma S2540T4deg : S2540T4.natDegree < 12 := by
  simp only [S2540T4]
  compute_degree!

lemma S2540T5deg : S2540T5.natDegree < 12 := by
  simp only [S2540T5]
  compute_degree!

lemma S2540T6deg : S2540T6.natDegree < 12 := by
  simp only [S2540T6]
  compute_degree!

lemma S2540T7deg : S2540T7.natDegree < 12 := by
  simp only [S2540T7]
  compute_degree!

lemma S2540T8deg : S2540T8.natDegree < 12 := by
  simp only [S2540T8]
  compute_degree!

lemma S2540T9deg : S2540T9.natDegree < 12 := by
  simp only [S2540T9]
  compute_degree!

lemma S2540T10deg : S2540T10.natDegree < 12 := by
  simp only [S2540T10]
  compute_degree!

lemma S2540T11deg : S2540T11.natDegree < 12 := by
  simp only [S2540T11]
  compute_degree!

lemma S2540T12deg : S2540T12.natDegree < 12 := by
  simp only [S2540T12]
  compute_degree!

lemma S2540T2sum : (∑ i ∈ Finset.range 12, C (S2540T1.coeff i) * S2540Dfun i) = S2540T2 := by
  ext k
  by_cases hk : k < 12
  · interval_cases k <;>
      (simp [S2540Dfun, S2540D0, S2540D1, S2540D2, S2540D3, S2540D4, S2540D5, S2540D6, S2540D7, S2540D8, S2540D9, S2540D10, S2540D11, S2540T1, S2540T2,
        coeff_sum, coeff_C_mul, coeff_add, coeff_one, coeff_monomial, coeff_X, coeff_X_pow,
        Finset.sum_range_succ] <;> decide)
  · have h1 : (∑ i ∈ Finset.range 12, C (S2540T1.coeff i) * S2540Dfun i).coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := S2540sum_deg S2540T1
      omega
    have h2 : S2540T2.coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := S2540T2deg
      omega
    rw [h1, h2]

lemma S2540T3sum : (∑ i ∈ Finset.range 12, C (S2540T2.coeff i) * S2540Dfun i) = S2540T3 := by
  ext k
  by_cases hk : k < 12
  · interval_cases k <;>
      (simp [S2540Dfun, S2540D0, S2540D1, S2540D2, S2540D3, S2540D4, S2540D5, S2540D6, S2540D7, S2540D8, S2540D9, S2540D10, S2540D11, S2540T2, S2540T3,
        coeff_sum, coeff_C_mul, coeff_add, coeff_one, coeff_monomial, coeff_X, coeff_X_pow,
        Finset.sum_range_succ] <;> decide)
  · have h1 : (∑ i ∈ Finset.range 12, C (S2540T2.coeff i) * S2540Dfun i).coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := S2540sum_deg S2540T2
      omega
    have h2 : S2540T3.coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := S2540T3deg
      omega
    rw [h1, h2]

lemma S2540T4sum : (∑ i ∈ Finset.range 12, C (S2540T3.coeff i) * S2540Dfun i) = S2540T4 := by
  ext k
  by_cases hk : k < 12
  · interval_cases k <;>
      (simp [S2540Dfun, S2540D0, S2540D1, S2540D2, S2540D3, S2540D4, S2540D5, S2540D6, S2540D7, S2540D8, S2540D9, S2540D10, S2540D11, S2540T3, S2540T4,
        coeff_sum, coeff_C_mul, coeff_add, coeff_one, coeff_monomial, coeff_X, coeff_X_pow,
        Finset.sum_range_succ] <;> decide)
  · have h1 : (∑ i ∈ Finset.range 12, C (S2540T3.coeff i) * S2540Dfun i).coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := S2540sum_deg S2540T3
      omega
    have h2 : S2540T4.coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := S2540T4deg
      omega
    rw [h1, h2]

lemma S2540T5sum : (∑ i ∈ Finset.range 12, C (S2540T4.coeff i) * S2540Dfun i) = S2540T5 := by
  ext k
  by_cases hk : k < 12
  · interval_cases k <;>
      (simp [S2540Dfun, S2540D0, S2540D1, S2540D2, S2540D3, S2540D4, S2540D5, S2540D6, S2540D7, S2540D8, S2540D9, S2540D10, S2540D11, S2540T4, S2540T5,
        coeff_sum, coeff_C_mul, coeff_add, coeff_one, coeff_monomial, coeff_X, coeff_X_pow,
        Finset.sum_range_succ] <;> decide)
  · have h1 : (∑ i ∈ Finset.range 12, C (S2540T4.coeff i) * S2540Dfun i).coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := S2540sum_deg S2540T4
      omega
    have h2 : S2540T5.coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := S2540T5deg
      omega
    rw [h1, h2]

lemma S2540T6sum : (∑ i ∈ Finset.range 12, C (S2540T5.coeff i) * S2540Dfun i) = S2540T6 := by
  ext k
  by_cases hk : k < 12
  · interval_cases k <;>
      (simp [S2540Dfun, S2540D0, S2540D1, S2540D2, S2540D3, S2540D4, S2540D5, S2540D6, S2540D7, S2540D8, S2540D9, S2540D10, S2540D11, S2540T5, S2540T6,
        coeff_sum, coeff_C_mul, coeff_add, coeff_one, coeff_monomial, coeff_X, coeff_X_pow,
        Finset.sum_range_succ] <;> decide)
  · have h1 : (∑ i ∈ Finset.range 12, C (S2540T5.coeff i) * S2540Dfun i).coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := S2540sum_deg S2540T5
      omega
    have h2 : S2540T6.coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := S2540T6deg
      omega
    rw [h1, h2]

lemma S2540T7sum : (∑ i ∈ Finset.range 12, C (S2540T6.coeff i) * S2540Dfun i) = S2540T7 := by
  ext k
  by_cases hk : k < 12
  · interval_cases k <;>
      (simp [S2540Dfun, S2540D0, S2540D1, S2540D2, S2540D3, S2540D4, S2540D5, S2540D6, S2540D7, S2540D8, S2540D9, S2540D10, S2540D11, S2540T6, S2540T7,
        coeff_sum, coeff_C_mul, coeff_add, coeff_one, coeff_monomial, coeff_X, coeff_X_pow,
        Finset.sum_range_succ] <;> decide)
  · have h1 : (∑ i ∈ Finset.range 12, C (S2540T6.coeff i) * S2540Dfun i).coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := S2540sum_deg S2540T6
      omega
    have h2 : S2540T7.coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := S2540T7deg
      omega
    rw [h1, h2]

lemma S2540T8sum : (∑ i ∈ Finset.range 12, C (S2540T7.coeff i) * S2540Dfun i) = S2540T8 := by
  ext k
  by_cases hk : k < 12
  · interval_cases k <;>
      (simp [S2540Dfun, S2540D0, S2540D1, S2540D2, S2540D3, S2540D4, S2540D5, S2540D6, S2540D7, S2540D8, S2540D9, S2540D10, S2540D11, S2540T7, S2540T8,
        coeff_sum, coeff_C_mul, coeff_add, coeff_one, coeff_monomial, coeff_X, coeff_X_pow,
        Finset.sum_range_succ] <;> decide)
  · have h1 : (∑ i ∈ Finset.range 12, C (S2540T7.coeff i) * S2540Dfun i).coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := S2540sum_deg S2540T7
      omega
    have h2 : S2540T8.coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := S2540T8deg
      omega
    rw [h1, h2]

lemma S2540T9sum : (∑ i ∈ Finset.range 12, C (S2540T8.coeff i) * S2540Dfun i) = S2540T9 := by
  ext k
  by_cases hk : k < 12
  · interval_cases k <;>
      (simp [S2540Dfun, S2540D0, S2540D1, S2540D2, S2540D3, S2540D4, S2540D5, S2540D6, S2540D7, S2540D8, S2540D9, S2540D10, S2540D11, S2540T8, S2540T9,
        coeff_sum, coeff_C_mul, coeff_add, coeff_one, coeff_monomial, coeff_X, coeff_X_pow,
        Finset.sum_range_succ] <;> decide)
  · have h1 : (∑ i ∈ Finset.range 12, C (S2540T8.coeff i) * S2540Dfun i).coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := S2540sum_deg S2540T8
      omega
    have h2 : S2540T9.coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := S2540T9deg
      omega
    rw [h1, h2]

lemma S2540T10sum : (∑ i ∈ Finset.range 12, C (S2540T9.coeff i) * S2540Dfun i) = S2540T10 := by
  ext k
  by_cases hk : k < 12
  · interval_cases k <;>
      (simp [S2540Dfun, S2540D0, S2540D1, S2540D2, S2540D3, S2540D4, S2540D5, S2540D6, S2540D7, S2540D8, S2540D9, S2540D10, S2540D11, S2540T9, S2540T10,
        coeff_sum, coeff_C_mul, coeff_add, coeff_one, coeff_monomial, coeff_X, coeff_X_pow,
        Finset.sum_range_succ] <;> decide)
  · have h1 : (∑ i ∈ Finset.range 12, C (S2540T9.coeff i) * S2540Dfun i).coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := S2540sum_deg S2540T9
      omega
    have h2 : S2540T10.coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := S2540T10deg
      omega
    rw [h1, h2]

lemma S2540T11sum : (∑ i ∈ Finset.range 12, C (S2540T10.coeff i) * S2540Dfun i) = S2540T11 := by
  ext k
  by_cases hk : k < 12
  · interval_cases k <;>
      (simp [S2540Dfun, S2540D0, S2540D1, S2540D2, S2540D3, S2540D4, S2540D5, S2540D6, S2540D7, S2540D8, S2540D9, S2540D10, S2540D11, S2540T10, S2540T11,
        coeff_sum, coeff_C_mul, coeff_add, coeff_one, coeff_monomial, coeff_X, coeff_X_pow,
        Finset.sum_range_succ] <;> decide)
  · have h1 : (∑ i ∈ Finset.range 12, C (S2540T10.coeff i) * S2540Dfun i).coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := S2540sum_deg S2540T10
      omega
    have h2 : S2540T11.coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := S2540T11deg
      omega
    rw [h1, h2]

lemma S2540T12sum : (∑ i ∈ Finset.range 12, C (S2540T11.coeff i) * S2540Dfun i) = S2540T12 := by
  ext k
  by_cases hk : k < 12
  · interval_cases k <;>
      (simp [S2540Dfun, S2540D0, S2540D1, S2540D2, S2540D3, S2540D4, S2540D5, S2540D6, S2540D7, S2540D8, S2540D9, S2540D10, S2540D11, S2540T11, S2540T12,
        coeff_sum, coeff_C_mul, coeff_add, coeff_one, coeff_monomial, coeff_X, coeff_X_pow,
        Finset.sum_range_succ] <;> decide)
  · have h1 : (∑ i ∈ Finset.range 12, C (S2540T11.coeff i) * S2540Dfun i).coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := S2540sum_deg S2540T11
      omega
    have h2 : S2540T12.coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := S2540T12deg
      omega
    rw [h1, h2]

lemma S2540T2comp : aeval (aeval S2540x S2540T1) S2540T1 = aeval S2540x S2540T2 :=
  S2540aeval_comp_sum (Q := S2540T1) (P := S2540T1) (Dfun := S2540Dfun) (W := S2540T2)
    S2540T1deg S2540D_aeval_all S2540T2sum

lemma S2540T3comp : aeval (aeval S2540x S2540T1) S2540T2 = aeval S2540x S2540T3 :=
  S2540aeval_comp_sum (Q := S2540T1) (P := S2540T2) (Dfun := S2540Dfun) (W := S2540T3)
    S2540T2deg S2540D_aeval_all S2540T3sum

lemma S2540T4comp : aeval (aeval S2540x S2540T1) S2540T3 = aeval S2540x S2540T4 :=
  S2540aeval_comp_sum (Q := S2540T1) (P := S2540T3) (Dfun := S2540Dfun) (W := S2540T4)
    S2540T3deg S2540D_aeval_all S2540T4sum

lemma S2540T5comp : aeval (aeval S2540x S2540T1) S2540T4 = aeval S2540x S2540T5 :=
  S2540aeval_comp_sum (Q := S2540T1) (P := S2540T4) (Dfun := S2540Dfun) (W := S2540T5)
    S2540T4deg S2540D_aeval_all S2540T5sum

lemma S2540T6comp : aeval (aeval S2540x S2540T1) S2540T5 = aeval S2540x S2540T6 :=
  S2540aeval_comp_sum (Q := S2540T1) (P := S2540T5) (Dfun := S2540Dfun) (W := S2540T6)
    S2540T5deg S2540D_aeval_all S2540T6sum

lemma S2540T7comp : aeval (aeval S2540x S2540T1) S2540T6 = aeval S2540x S2540T7 :=
  S2540aeval_comp_sum (Q := S2540T1) (P := S2540T6) (Dfun := S2540Dfun) (W := S2540T7)
    S2540T6deg S2540D_aeval_all S2540T7sum

lemma S2540T8comp : aeval (aeval S2540x S2540T1) S2540T7 = aeval S2540x S2540T8 :=
  S2540aeval_comp_sum (Q := S2540T1) (P := S2540T7) (Dfun := S2540Dfun) (W := S2540T8)
    S2540T7deg S2540D_aeval_all S2540T8sum

lemma S2540T9comp : aeval (aeval S2540x S2540T1) S2540T8 = aeval S2540x S2540T9 :=
  S2540aeval_comp_sum (Q := S2540T1) (P := S2540T8) (Dfun := S2540Dfun) (W := S2540T9)
    S2540T8deg S2540D_aeval_all S2540T9sum

lemma S2540T10comp : aeval (aeval S2540x S2540T1) S2540T9 = aeval S2540x S2540T10 :=
  S2540aeval_comp_sum (Q := S2540T1) (P := S2540T9) (Dfun := S2540Dfun) (W := S2540T10)
    S2540T9deg S2540D_aeval_all S2540T10sum

lemma S2540T11comp : aeval (aeval S2540x S2540T1) S2540T10 = aeval S2540x S2540T11 :=
  S2540aeval_comp_sum (Q := S2540T1) (P := S2540T10) (Dfun := S2540Dfun) (W := S2540T11)
    S2540T10deg S2540D_aeval_all S2540T11sum

lemma S2540T12comp : aeval (aeval S2540x S2540T1) S2540T11 = aeval S2540x S2540T12 :=
  S2540aeval_comp_sum (Q := S2540T1) (P := S2540T11) (Dfun := S2540Dfun) (W := S2540T12)
    S2540T11deg S2540D_aeval_all S2540T12sum


/-! ## 9. The Frobenius chain -/

lemma S2540spec1 : S2540x ^ 613 = aeval S2540x S2540T1 := S2540aeval_X_pow_eq S2540h613

lemma S2540spec2 : S2540x ^ (613 ^ 2) = aeval S2540x S2540T2 := by
  have hcomp : aeval (aeval S2540x S2540T1) S2540T1 = aeval S2540x S2540T2 :=
    S2540T2comp
  calc S2540x ^ (613 ^ 2) = (S2540x ^ (613 ^ 1)) ^ 613 := by
        rw [← pow_mul, ← pow_succ]
    _ = (aeval S2540x S2540T1) ^ 613 := by rw [S2540spec1]
    _ = aeval (S2540x ^ 613) S2540T1 := S2540aeval_pow_char S2540x S2540T1
    _ = aeval (aeval S2540x S2540T1) S2540T1 := by rw [S2540spec1]
    _ = aeval S2540x S2540T2 := hcomp

lemma S2540spec3 : S2540x ^ (613 ^ 3) = aeval S2540x S2540T3 := by
  have hcomp : aeval (aeval S2540x S2540T1) S2540T2 = aeval S2540x S2540T3 :=
    S2540T3comp
  calc S2540x ^ (613 ^ 3) = (S2540x ^ (613 ^ 2)) ^ 613 := by
        rw [← pow_mul, ← pow_succ]
    _ = (aeval S2540x S2540T2) ^ 613 := by rw [S2540spec2]
    _ = aeval (S2540x ^ 613) S2540T2 := S2540aeval_pow_char S2540x S2540T2
    _ = aeval (aeval S2540x S2540T1) S2540T2 := by rw [S2540spec1]
    _ = aeval S2540x S2540T3 := hcomp

lemma S2540spec4 : S2540x ^ (613 ^ 4) = aeval S2540x S2540T4 := by
  have hcomp : aeval (aeval S2540x S2540T1) S2540T3 = aeval S2540x S2540T4 :=
    S2540T4comp
  calc S2540x ^ (613 ^ 4) = (S2540x ^ (613 ^ 3)) ^ 613 := by
        rw [← pow_mul, ← pow_succ]
    _ = (aeval S2540x S2540T3) ^ 613 := by rw [S2540spec3]
    _ = aeval (S2540x ^ 613) S2540T3 := S2540aeval_pow_char S2540x S2540T3
    _ = aeval (aeval S2540x S2540T1) S2540T3 := by rw [S2540spec1]
    _ = aeval S2540x S2540T4 := hcomp

lemma S2540spec5 : S2540x ^ (613 ^ 5) = aeval S2540x S2540T5 := by
  have hcomp : aeval (aeval S2540x S2540T1) S2540T4 = aeval S2540x S2540T5 :=
    S2540T5comp
  calc S2540x ^ (613 ^ 5) = (S2540x ^ (613 ^ 4)) ^ 613 := by
        rw [← pow_mul, ← pow_succ]
    _ = (aeval S2540x S2540T4) ^ 613 := by rw [S2540spec4]
    _ = aeval (S2540x ^ 613) S2540T4 := S2540aeval_pow_char S2540x S2540T4
    _ = aeval (aeval S2540x S2540T1) S2540T4 := by rw [S2540spec1]
    _ = aeval S2540x S2540T5 := hcomp

lemma S2540spec6 : S2540x ^ (613 ^ 6) = aeval S2540x S2540T6 := by
  have hcomp : aeval (aeval S2540x S2540T1) S2540T5 = aeval S2540x S2540T6 :=
    S2540T6comp
  calc S2540x ^ (613 ^ 6) = (S2540x ^ (613 ^ 5)) ^ 613 := by
        rw [← pow_mul, ← pow_succ]
    _ = (aeval S2540x S2540T5) ^ 613 := by rw [S2540spec5]
    _ = aeval (S2540x ^ 613) S2540T5 := S2540aeval_pow_char S2540x S2540T5
    _ = aeval (aeval S2540x S2540T1) S2540T5 := by rw [S2540spec1]
    _ = aeval S2540x S2540T6 := hcomp

lemma S2540spec7 : S2540x ^ (613 ^ 7) = aeval S2540x S2540T7 := by
  have hcomp : aeval (aeval S2540x S2540T1) S2540T6 = aeval S2540x S2540T7 :=
    S2540T7comp
  calc S2540x ^ (613 ^ 7) = (S2540x ^ (613 ^ 6)) ^ 613 := by
        rw [← pow_mul, ← pow_succ]
    _ = (aeval S2540x S2540T6) ^ 613 := by rw [S2540spec6]
    _ = aeval (S2540x ^ 613) S2540T6 := S2540aeval_pow_char S2540x S2540T6
    _ = aeval (aeval S2540x S2540T1) S2540T6 := by rw [S2540spec1]
    _ = aeval S2540x S2540T7 := hcomp

lemma S2540spec8 : S2540x ^ (613 ^ 8) = aeval S2540x S2540T8 := by
  have hcomp : aeval (aeval S2540x S2540T1) S2540T7 = aeval S2540x S2540T8 :=
    S2540T8comp
  calc S2540x ^ (613 ^ 8) = (S2540x ^ (613 ^ 7)) ^ 613 := by
        rw [← pow_mul, ← pow_succ]
    _ = (aeval S2540x S2540T7) ^ 613 := by rw [S2540spec7]
    _ = aeval (S2540x ^ 613) S2540T7 := S2540aeval_pow_char S2540x S2540T7
    _ = aeval (aeval S2540x S2540T1) S2540T7 := by rw [S2540spec1]
    _ = aeval S2540x S2540T8 := hcomp

lemma S2540spec9 : S2540x ^ (613 ^ 9) = aeval S2540x S2540T9 := by
  have hcomp : aeval (aeval S2540x S2540T1) S2540T8 = aeval S2540x S2540T9 :=
    S2540T9comp
  calc S2540x ^ (613 ^ 9) = (S2540x ^ (613 ^ 8)) ^ 613 := by
        rw [← pow_mul, ← pow_succ]
    _ = (aeval S2540x S2540T8) ^ 613 := by rw [S2540spec8]
    _ = aeval (S2540x ^ 613) S2540T8 := S2540aeval_pow_char S2540x S2540T8
    _ = aeval (aeval S2540x S2540T1) S2540T8 := by rw [S2540spec1]
    _ = aeval S2540x S2540T9 := hcomp

lemma S2540spec10 : S2540x ^ (613 ^ 10) = aeval S2540x S2540T10 := by
  have hcomp : aeval (aeval S2540x S2540T1) S2540T9 = aeval S2540x S2540T10 :=
    S2540T10comp
  calc S2540x ^ (613 ^ 10) = (S2540x ^ (613 ^ 9)) ^ 613 := by
        rw [← pow_mul, ← pow_succ]
    _ = (aeval S2540x S2540T9) ^ 613 := by rw [S2540spec9]
    _ = aeval (S2540x ^ 613) S2540T9 := S2540aeval_pow_char S2540x S2540T9
    _ = aeval (aeval S2540x S2540T1) S2540T9 := by rw [S2540spec1]
    _ = aeval S2540x S2540T10 := hcomp

lemma S2540spec11 : S2540x ^ (613 ^ 11) = aeval S2540x S2540T11 := by
  have hcomp : aeval (aeval S2540x S2540T1) S2540T10 = aeval S2540x S2540T11 :=
    S2540T11comp
  calc S2540x ^ (613 ^ 11) = (S2540x ^ (613 ^ 10)) ^ 613 := by
        rw [← pow_mul, ← pow_succ]
    _ = (aeval S2540x S2540T10) ^ 613 := by rw [S2540spec10]
    _ = aeval (S2540x ^ 613) S2540T10 := S2540aeval_pow_char S2540x S2540T10
    _ = aeval (aeval S2540x S2540T1) S2540T10 := by rw [S2540spec1]
    _ = aeval S2540x S2540T11 := hcomp

lemma S2540spec12 : S2540x ^ (613 ^ 12) = aeval S2540x S2540T12 := by
  have hcomp : aeval (aeval S2540x S2540T1) S2540T11 = aeval S2540x S2540T12 :=
    S2540T12comp
  calc S2540x ^ (613 ^ 12) = (S2540x ^ (613 ^ 11)) ^ 613 := by
        rw [← pow_mul, ← pow_succ]
    _ = (aeval S2540x S2540T11) ^ 613 := by rw [S2540spec11]
    _ = aeval (S2540x ^ 613) S2540T11 := S2540aeval_pow_char S2540x S2540T11
    _ = aeval (aeval S2540x S2540T1) S2540T11 := by rw [S2540spec1]
    _ = aeval S2540x S2540T12 := hcomp

/-! ## 10. Coprimality, divisibility and the main theorem -/

lemma S2540isCoprimeT4 : IsCoprime S2540F (S2540T4 - X) :=
  ⟨S2540P4, S2540Q4, S2540certP4⟩

lemma S2540isCoprimeT6 : IsCoprime S2540F (S2540T6 - X) :=
  ⟨S2540P6, S2540Q6, S2540certP6⟩

lemma S2540dvd4 : S2540F ∣ (X : (ZMod 613)[X]) ^ 613 ^ 4 - S2540T4 := by
  apply S2540dvd_of_aeval_eq_zero
  rw [map_sub, map_pow, Polynomial.aeval_X, S2540spec4, sub_self]

lemma S2540dvd6 : S2540F ∣ (X : (ZMod 613)[X]) ^ 613 ^ 6 - S2540T6 := by
  apply S2540dvd_of_aeval_eq_zero
  rw [map_sub, map_pow, Polynomial.aeval_X, S2540spec6, sub_self]

lemma S2540h4cop : IsCoprime S2540F ((X : (ZMod 613)[X]) ^ 613 ^ 4 - X) := by
  have hd : S2540F ∣ ((X : (ZMod 613)[X]) ^ 613 ^ 4 - X) - (S2540T4 - X) := by
    rw [show ((X : (ZMod 613)[X]) ^ 613 ^ 4 - X) - (S2540T4 - X) =
      (X : (ZMod 613)[X]) ^ 613 ^ 4 - S2540T4 by ring]
    exact S2540dvd4
  exact S2540isCoprime_of_dvd_sub S2540isCoprimeT4 hd

lemma S2540h6cop : IsCoprime S2540F ((X : (ZMod 613)[X]) ^ 613 ^ 6 - X) := by
  have hd : S2540F ∣ ((X : (ZMod 613)[X]) ^ 613 ^ 6 - X) - (S2540T6 - X) := by
    rw [show ((X : (ZMod 613)[X]) ^ 613 ^ 6 - X) - (S2540T6 - X) =
      (X : (ZMod 613)[X]) ^ 613 ^ 6 - S2540T6 by ring]
    exact S2540dvd6
  exact S2540isCoprime_of_dvd_sub S2540isCoprimeT6 hd

lemma S2540hdvd : S2540F ∣ (X : (ZMod 613)[X]) ^ 613 ^ 12 - X := by
  apply S2540dvd_of_aeval_eq_zero
  rw [map_sub, map_pow, Polynomial.aeval_X, S2540spec12]
  simp [S2540T12]

lemma S2540card : Nat.card (ZMod 613) = 613 := by
  rw [Nat.card_eq_fintype_card, ZMod.card]

lemma S2540hdvdCard : S2540F ∣ (X : (ZMod 613)[X]) ^ Nat.card (ZMod 613) ^ 12 - X := by
  rw [S2540card]
  exact S2540hdvd

lemma S2540h4copCard :
    IsCoprime S2540F ((X : (ZMod 613)[X]) ^ Nat.card (ZMod 613) ^ 4 - X) := by
  rw [S2540card]
  exact S2540h4cop

lemma S2540h6copCard :
    IsCoprime S2540F ((X : (ZMod 613)[X]) ^ Nat.card (ZMod 613) ^ 6 - X) := by
  rw [S2540card]
  exact S2540h6cop

theorem S2540F_irreducible : Irreducible S2540F :=
  S2540irreducible_of_degree_twelve (K := ZMod 613)
    S2540F_natDegree S2540hdvdCard S2540h4copCard S2540h6copCard

/-- The residue certificate: the mod-613 reduction of the degree-twelve integer
model of psi_5 is irreducible. -/
theorem S2540ResidueCertificate :
    Irreducible (S2132Psi5Z.map (Int.castRingHom (ZMod 613))) := by
  rw [S2540F_eq_target]
  exact S2540F_irreducible

/-- The certificate in the exact form in which it was isolated in S2481. -/
theorem S2540S2481ResidueCertificate : S2481ResidueCertificate := by
  unfold S2481ResidueCertificate
  exact S2540ResidueCertificate


end LeanFormal.IUT.XiFPaper.S2540Mod613CertificateActual

end
