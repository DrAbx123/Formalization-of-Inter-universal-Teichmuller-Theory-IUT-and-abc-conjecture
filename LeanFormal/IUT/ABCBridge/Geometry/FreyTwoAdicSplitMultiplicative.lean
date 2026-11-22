/-
# Split versus non-split multiplicative reduction at `2` for the halved Frey model

Proves the two cards `FreyTwoAdicSplitMultiplicativeStatement` and
`FreyTwoAdicNonSplitMultiplicativeStatement` of `FreyTwoAdicMinimalReduction.lean`.

On the multiplicative family (`b = a + 1 + 4m`, `ab = 16n`, `n` even) the integral model of
the halved curve is `(1, m, 0, -n, 0)`.  Mathlib's splitting polynomial
`c₄ X² + a₁ c₄ X - (54 b₆ - 3 b₂ b₄ + a₂ c₄)` reduces over the residue field `𝔽₂` to
`X² + X + m`, which splits iff `m` is even.  For `a ≡ 7 (mod 8)` (so `16 ∣ b`) `m` is even;
for `a ≡ 3 (mod 8)` `m` is odd and `X² + X + 1` has no root in `𝔽₂`.
-/

import LeanFormal.IUT.ABCBridge.Geometry.FreyTwoAdicMinimalReduction
import Mathlib.NumberTheory.Padics.RingHoms

noncomputable section

open Polynomial

namespace LeanFormal.IUT

/-- The coefficients of Mathlib's integral model of the halved curve. -/
theorem freyTwoAdicHalvingModel_integralModel_coeffs {a b : ℕ} {m : ℤ} {n : ℕ}
    (hb : (b : ℤ) = (a : ℤ) + 1 + 4 * m) (hab : a * b = 16 * n)
    [WeierstrassCurve.IsIntegral ℤ_[2] (freyTwoAdicHalvingModel a b)] :
    let I := (freyTwoAdicHalvingModel a b).integralModel ℤ_[2]
    I.a₁ = 1 ∧ I.a₂ = (m : ℤ_[2]) ∧ I.a₃ = 0 ∧ I.a₄ = -(n : ℤ_[2]) ∧ I.a₆ = 0 := by
  intro I
  have hinj := IsFractionRing.injective ℤ_[2] ℚ_[2]
  have hb' : (b : ℚ_[2]) = (a : ℚ_[2]) + 1 + 4 * (m : ℚ_[2]) := by
    have h := congrArg (fun z : ℤ => (z : ℚ_[2])) hb
    push_cast at h
    exact h
  have hab' : (a : ℚ_[2]) * b = 16 * (n : ℚ_[2]) := by
    have h := congrArg (fun z : ℕ => (z : ℚ_[2])) hab
    push_cast at h
    exact h
  refine ⟨hinj ?_, hinj ?_, hinj ?_, hinj ?_, hinj ?_⟩
  · rw [WeierstrassCurve.integralModel_a₁_eq, freyTwoAdicHalvingModel_a₁, map_one]
  · rw [WeierstrassCurve.integralModel_a₂_eq, freyTwoAdicHalvingModel_a₂, map_intCast, hb']
    ring
  · rw [WeierstrassCurve.integralModel_a₃_eq, freyTwoAdicHalvingModel_a₃, map_zero]
  · rw [WeierstrassCurve.integralModel_a₄_eq, freyTwoAdicHalvingModel_a₄, map_neg,
      map_natCast, hab']
    ring
  · rw [WeierstrassCurve.integralModel_a₆_eq, freyTwoAdicHalvingModel_a₆, map_zero]

/-- The reduction of the splitting polynomial of the halved model to `ZMod 2`. -/
theorem freyTwoAdicHalvingModel_splittingPolynomial_toZMod {a b : ℕ} {m : ℤ} {n : ℕ}
    (hb : (b : ℤ) = (a : ℤ) + 1 + 4 * m) (hab : a * b = 16 * n)
    [WeierstrassCurve.IsIntegral ℤ_[2] (freyTwoAdicHalvingModel a b)] :
    let I := (freyTwoAdicHalvingModel a b).integralModel ℤ_[2]
    (C I.c₄ * X ^ 2 + C (I.a₁ * I.c₄) * X -
        C (54 * I.b₆ - 3 * I.b₂ * I.b₄ + I.a₂ * I.c₄)).map (PadicInt.toZMod (p := 2)) =
      X ^ 2 + X - C (m : ZMod 2) := by
  intro I
  obtain ⟨h1, h2, h3, h4, h6⟩ := freyTwoAdicHalvingModel_integralModel_coeffs hb hab
  have key : ∀ M N : ZMod 2,
      (((1 : ZMod 2) ^ 2 + 4 * M) ^ 2 - 24 * (2 * -N + 1 * 0)) = 1 ∧
      (1 * (((1 : ZMod 2) ^ 2 + 4 * M) ^ 2 - 24 * (2 * -N + 1 * 0))) = 1 ∧
      (54 * ((0 : ZMod 2) ^ 2 + 4 * 0) - 3 * ((1 : ZMod 2) ^ 2 + 4 * M) * (2 * -N + 1 * 0) +
        M * (((1 : ZMod 2) ^ 2 + 4 * M) ^ 2 - 24 * (2 * -N + 1 * 0))) = M := by
    decide
  obtain ⟨k1, k2, k3⟩ := key (m : ZMod 2) (n : ZMod 2)
  have hc4 : PadicInt.toZMod (p := 2) I.c₄ = 1 := by
    simp only [I, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, h1, h2, h3, h4,
      map_sub, map_add, map_mul, map_pow, map_neg, map_one, map_zero, map_ofNat, map_intCast,
      map_natCast]
    exact k1
  have hc41 : PadicInt.toZMod (p := 2) (I.a₁ * I.c₄) = 1 := by
    simp only [I, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, h1, h2, h3, h4,
      map_sub, map_add, map_mul, map_pow, map_neg, map_one, map_zero, map_ofNat, map_intCast,
      map_natCast]
    exact k2
  have hconst : PadicInt.toZMod (p := 2) (54 * I.b₆ - 3 * I.b₂ * I.b₄ + I.a₂ * I.c₄) =
      (m : ZMod 2) := by
    simp only [I, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, h1, h2, h3, h4, h6,
      map_sub, map_add, map_mul, map_pow, map_neg, map_one, map_zero, map_ofNat, map_intCast,
      map_natCast]
    exact k3
  rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_C, Polynomial.map_C, Polynomial.map_X,
    hc4, hc41, hconst]
  simp

/-- `PadicInt.toZMod` factors through the residue field. -/
theorem padicInt_two_residue_map_eq (P : ℤ_[2][X]) :
    (P.map (IsLocalRing.residue ℤ_[2])).map (PadicInt.residueField (p := 2)).toRingHom =
      P.map (PadicInt.toZMod (p := 2)) := by
  rw [Polynomial.map_map, PadicInt.toZMod_eq_residueField_comp_residue]

/-- Splitting over the residue field is equivalent to splitting after the transfer to
`ZMod 2`. -/
theorem padicInt_two_splits_residue_iff (P : ℤ_[2][X]) :
    Splits (P.map (algebraMap ℤ_[2] (IsLocalRing.ResidueField ℤ_[2]))) ↔
      Splits (P.map (PadicInt.toZMod (p := 2))) := by
  rw [IsLocalRing.ResidueField.algebraMap_eq, ← padicInt_two_residue_map_eq]
  constructor
  · intro h
    exact h.map _
  · intro h
    have := h.map (PadicInt.residueField (p := 2)).symm.toRingHom
    rwa [Polynomial.map_map, RingEquiv.symm_toRingHom_comp_toRingHom, Polynomial.map_id] at this

/-- **Card (REPORT §3.3) proved: split multiplicative reduction for `a ≡ 7 (mod 8)`.** -/
theorem freyTwoAdicSplitMultiplicativeStatement_proved :
    FreyTwoAdicSplitMultiplicativeStatement := by
  rintro a b ⟨m, hb⟩ ⟨n, hab, hn⟩ ha8
  haveI hmult := freyTwoAdicHalvingModel_hasMultiplicativeReduction_of_congruences hb hab hn
  refine { toHasMultiplicativeReduction := hmult, splitMultiplicativeReduction := ?_ }
  rw [padicInt_two_splits_residue_iff, freyTwoAdicHalvingModel_splittingPolynomial_toZMod hb hab]
  have hcop : Nat.Coprime 16 a :=
    Nat.Coprime.pow_left 4 (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega)))
  have h16 : 16 ∣ b := hcop.dvd_of_dvd_mul_left ⟨n, hab⟩
  obtain ⟨j, hj⟩ : 2 ∣ m := by omega
  have hm0 : (m : ZMod 2) = 0 := by
    rw [hj]
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]
  rw [hm0, map_zero, sub_zero, show (X ^ 2 + X : (ZMod 2)[X]) = X * (X + C 1) by
    rw [map_one]; ring]
  exact Splits.X.mul (Splits.X_add_C 1)

/-- **Card (REPORT §3.3) proved: non-split multiplicative reduction for `a ≡ 3 (mod 8)`.** -/
theorem freyTwoAdicNonSplitMultiplicativeStatement_proved :
    FreyTwoAdicNonSplitMultiplicativeStatement := by
  rintro a b ⟨m, hb⟩ ⟨n, hab, hn⟩ ha8 hsplit
  haveI : WeierstrassCurve.IsIntegral ℤ_[2] (freyTwoAdicHalvingModel a b) :=
    freyTwoAdicHalvingModel_isIntegral_of_congruences hb hab
  have hs := hsplit.splitMultiplicativeReduction
  rw [padicInt_two_splits_residue_iff, freyTwoAdicHalvingModel_splittingPolynomial_toZMod hb hab]
    at hs
  have hcop : Nat.Coprime 16 a :=
    Nat.Coprime.pow_left 4 (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega)))
  have h16 : 16 ∣ b := hcop.dvd_of_dvd_mul_left ⟨n, hab⟩
  obtain ⟨j, hj⟩ : ∃ j, m = 2 * j + 1 := ⟨(m - 1) / 2, by omega⟩
  have hm1 : (m : ZMod 2) = 1 := by
    rw [hj]
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
  rw [hm1] at hs
  have hnat : (X ^ 2 + X - C (1 : ZMod 2)).natDegree = 2 := by compute_degree!
  have hdeg : (X ^ 2 + X - C (1 : ZMod 2)).degree ≠ 0 := by
    intro h
    have := Polynomial.natDegree_eq_of_degree_eq_some h
    rw [hnat] at this
    exact absurd this (by norm_num)
  obtain ⟨r, hr⟩ := hs.exists_eval_eq_zero hdeg
  simp only [eval_sub, eval_add, eval_pow, eval_X, eval_C] at hr
  revert hr
  revert r
  decide

end LeanFormal.IUT
