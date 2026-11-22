/-
# 2-adic minimal discriminant valuation of the displayed ABC Frey model

For the displayed abc-Frey curve `freyPadicCurve 2 a b` over `ℚ_[2]`, this
file provides:

* the transfer lemmas for Mathlib's `WeierstrassCurve.valuation_Δ_aux`:
  an integral model related to a minimal model by an integral variable change
  has `Δ`-valuation at most that of the minimal model, and any two minimal
  integral models related by a variable change have the same `Δ`-valuation;
* the bridge from `PadicInt.valuation` at `p = 2` to `padicValNat`, so that
  the discrete valuation of a nonzero natural cast is `exp (-v₂)`;
* the definition `freyTwoAdicMinimalDiscriminantValuation a b`, the
  `v₂(Δ_min)` of the displayed model, as the `Δ`-valuation of Mathlib's
  chosen minimal model `(freyPadicCurve 2 a b).minimal ℤ_[2]`, together with
  the agreement lemmas for arbitrary minimal integral models and for the
  explicit halved model in the family `b = a + 1 + 4 * m`, `a * b = 16 * n`.

Literature freeze (statement-level, not re-derived here): Silverman,
*Advanced Topics in the Arithmetic of Elliptic Curves*, IV.9 and IV.10;
Saito 1988 (conductor-discriminant exponents).  The `m₂` and `swan₂`
exponents are NOT formalized in this file and no numerical claim about them
is made or endorsed; see `tmp/dsh-2adic-minimal-model-20261016/REPORT.md`.
-/

import LeanFormal.IUT.ABCBridge.Geometry.FreyTwoAdicMinimalReduction
import Mathlib.NumberTheory.Padics.PadicIntegers

noncomputable section

open scoped WeierstrassCurve WithZero

namespace LeanFormal.IUT

/-! ## Transfer lemmas for minimal models -/

/-- An integral model related by a variable change to a minimal model has
`Delta`-valuation at most that of the minimal model. -/
theorem valuation_Δ_aux_le_of_isMinimal {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] (W : WeierstrassCurve K) [WeierstrassCurve.IsMinimal R W]
    (C : WeierstrassCurve.VariableChange K) [WeierstrassCurve.IsIntegral R (C • W)] :
    WeierstrassCurve.valuation_Δ_aux R (C • W) ≤
      WeierstrassCurve.valuation_Δ_aux R W := by
  have h := (inferInstance : WeierstrassCurve.IsMinimal R W).val_Δ_maximal.2
    (inferInstance : WeierstrassCurve.IsIntegral R (C • W))
  rcases le_total (WeierstrassCurve.valuation_Δ_aux R (C • W))
      (WeierstrassCurve.valuation_Δ_aux R
        ((1 : WeierstrassCurve.VariableChange K) • W)) with hle | hle
  · simpa only [one_smul] using hle
  · simpa only [one_smul] using h hle

/-- Two minimal models related by a variable change have equal
`Delta`-valuation. -/
theorem valuation_Δ_aux_eq_of_isMinimal {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] {W : WeierstrassCurve K} [WeierstrassCurve.IsMinimal R W]
    (C : WeierstrassCurve.VariableChange K) [WeierstrassCurve.IsMinimal R (C • W)] :
    WeierstrassCurve.valuation_Δ_aux R (C • W) =
      WeierstrassCurve.valuation_Δ_aux R W := by
  apply le_antisymm
  · exact valuation_Δ_aux_le_of_isMinimal (R := R) (K := K) W C
  · haveI hI : WeierstrassCurve.IsIntegral R (C⁻¹ • (C • W)) := by
      rw [inv_smul_smul]
      infer_instance
    have h := valuation_Δ_aux_le_of_isMinimal (R := R) (K := K) (W := C • W) C⁻¹
    simpa only [inv_smul_smul] using h

/-! ## 2-adic valuation bridges -/

/-- `PadicInt.valuation` of a nonzero natural cast is `padicValNat 2`. -/
theorem padicInt_valuation_natCast_eq_padicValNat {n : ℕ} (hn : n ≠ 0) :
    (n : ℤ_[2]).valuation = padicValNat 2 n := by
  have hiff : ∀ m : ℕ, m ≤ (n : ℤ_[2]).valuation ↔ m ≤ padicValNat 2 n := by
    intro m
    rw [← PadicInt.mem_span_pow_iff_le_valuation (n : ℤ_[2])
        (Nat.cast_ne_zero.mpr hn) m,
      Ideal.mem_span_singleton,
      show (n : ℤ_[2]) = ((n : ℤ) : ℤ_[2]) by rw [Int.cast_natCast],
      PadicInt.pow_p_dvd_int_iff, ← Nat.cast_pow, Int.natCast_dvd_natCast,
      pow_dvd_iff_le_emultiplicity,
      ← padicValNat_eq_emultiplicity (p := 2) hn]
    exact Nat.cast_le
  exact le_antisymm ((hiff _).mp le_rfl) ((hiff _).mpr le_rfl)

/-- The maximal-ideal valuation of a nonzero natural cast is
`exp (-padicValNat 2)`. -/
theorem padicInt_intValuation_natCast_eq_exp_neg {n : ℕ} (hn : n ≠ 0) :
    (IsDiscreteValuationRing.maximalIdeal ℤ_[2]).intValuation (n : ℤ_[2]) =
      WithZero.exp (-((padicValNat 2 n : ℕ) : ℤ)) := by
  have hval : (n : ℤ_[2]).valuation = padicValNat 2 n :=
    padicInt_valuation_natCast_eq_padicValNat hn
  have hasIdeal : (IsDiscreteValuationRing.maximalIdeal ℤ_[2]).asIdeal =
      Ideal.span {((2 : ℕ) : ℤ_[2])} := by
    rw [show (IsDiscreteValuationRing.maximalIdeal ℤ_[2]).asIdeal =
        IsLocalRing.maximalIdeal ℤ_[2] from rfl]
    exact PadicInt.maximalIdeal_eq_span_p
  have hmem : ∀ m : ℕ,
      (IsDiscreteValuationRing.maximalIdeal ℤ_[2]).intValuation (n : ℤ_[2]) ≤
        WithZero.exp (-(m : ℤ)) ↔ m ≤ padicValNat 2 n := by
    intro m
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem, hasIdeal,
      Ideal.span_singleton_pow]
    exact (PadicInt.mem_span_pow_iff_le_valuation (n : ℤ_[2])
      (Nat.cast_ne_zero.mpr hn) m).trans (by rw [hval])
  have h1 := (hmem (padicValNat 2 n)).mpr le_rfl
  have h2 : ¬ (IsDiscreteValuationRing.maximalIdeal ℤ_[2]).intValuation
      (n : ℤ_[2]) ≤
      WithZero.exp (-((padicValNat 2 n + 1 : ℕ) : ℤ)) := by
    rw [hmem]
    omega
  have hne : (IsDiscreteValuationRing.maximalIdeal ℤ_[2]).intValuation
      (n : ℤ_[2]) ≠ 0 :=
    IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero _ _
      (Nat.cast_ne_zero.mpr hn)
  have h3 : WithZero.exp (-((padicValNat 2 n : ℕ) : ℤ)) ≤
      (IsDiscreteValuationRing.maximalIdeal ℤ_[2]).intValuation (n : ℤ_[2]) := by
    have hlt := lt_of_not_ge h2
    rw [show (IsDiscreteValuationRing.maximalIdeal ℤ_[2]).intValuation
        (n : ℤ_[2]) =
        WithZero.exp ((IsDiscreteValuationRing.maximalIdeal ℤ_[2]).intValuation
          (n : ℤ_[2])).log from (WithZero.exp_log hne).symm]
    rw [WithZero.exp_le_exp]
    rw [show (IsDiscreteValuationRing.maximalIdeal ℤ_[2]).intValuation
        (n : ℤ_[2]) =
        WithZero.exp ((IsDiscreteValuationRing.maximalIdeal ℤ_[2]).intValuation
          (n : ℤ_[2])).log from (WithZero.exp_log hne).symm] at hlt
    rw [WithZero.exp_lt_exp] at hlt
    omega
  exact le_antisymm h1 h3

/-- The DVR valuation used by the reduction predicates takes the value
`exp (-padicValNat 2)` on nonzero natural casts. -/
theorem freyPadicValuation_two_natCast_eq_exp_neg_padicValNat {n : ℕ} (hn : n ≠ 0) :
    freyPadicValuation 2 (n : ℚ_[2]) =
      WithZero.exp (-((padicValNat 2 n : ℕ) : ℤ)) := by
  rw [show (n : ℚ_[2]) = algebraMap ℤ_[2] ℚ_[2] (n : ℤ_[2]) by
    exact (map_natCast (algebraMap ℤ_[2] ℚ_[2]) n).symm]
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact padicInt_intValuation_natCast_eq_exp_neg hn

/-- The `Delta`-change formula factors through the unit `u` of the variable
change only. -/
theorem freyPadicValuation_delta_variableChange (p : ℕ) [Fact p.Prime]
    (W : WeierstrassCurve ℚ_[p]) (C : WeierstrassCurve.VariableChange ℚ_[p]) :
    freyPadicValuation p (C • W).Δ =
      (freyPadicValuation p (C.u : ℚ_[p]))⁻¹ ^ 12 *
        freyPadicValuation p W.Δ := by
  rw [WeierstrassCurve.variableChange_Δ, map_mul, map_pow,
    Units.val_inv_eq_inv_val, Valuation.map_inv]

/-! ## The definition of v₂(Δ_min) -/

/-- `v₂(Δ_min)`: the `Δ`-valuation of a minimal model of the displayed Frey
curve over `ℚ_[2]`, i.e. the 2-adic valuation of the minimal discriminant. -/
noncomputable def freyTwoAdicMinimalDiscriminantValuation (a b : ℕ) : ℤᵐ⁰ :=
  freyPadicValuation 2 ((freyPadicCurve 2 a b).minimal ℤ_[2]).Δ

/-- The underlying value of `valuation_Δ_aux` for an integral model is the
`freyPadicValuation` of its discriminant. -/
theorem freyPadicValuation_eq_valuation_Δ_aux_val (W : WeierstrassCurve ℚ_[2])
    [WeierstrassCurve.IsIntegral ℤ_[2] W] :
    (WeierstrassCurve.valuation_Δ_aux ℤ_[2] W).val = freyPadicValuation 2 W.Δ := by
  rw [WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral]

/-- Any minimal integral model of the displayed Frey curve has the same
`Δ`-valuation as Mathlib's chosen minimal model. -/
theorem freyTwoAdicMinimalDiscriminantValuation_eq_of_variableChange_isMinimal
    (a b : ℕ) (C : WeierstrassCurve.VariableChange ℚ_[2])
    [hC : WeierstrassCurve.IsMinimal ℤ_[2] (C • freyPadicCurve 2 a b)] :
    freyTwoAdicMinimalDiscriminantValuation a b =
      freyPadicValuation 2 (C • freyPadicCurve 2 a b).Δ := by
  let W : WeierstrassCurve ℚ_[2] := freyPadicCurve 2 a b
  let C₀ : WeierstrassCurve.VariableChange ℚ_[2] := (W.exists_isMinimal ℤ_[2]).choose
  haveI hmin₀ : WeierstrassCurve.IsMinimal ℤ_[2] (C₀ • W) :=
    (W.exists_isMinimal ℤ_[2]).choose_spec
  have hsmul : (C₀ * C⁻¹) • (C • W) = C₀ • W := by
    rw [mul_smul, inv_smul_smul]
  haveI : WeierstrassCurve.IsMinimal ℤ_[2] ((C₀ * C⁻¹) • (C • W)) := by
    rw [hsmul]
    exact hmin₀
  have haux := valuation_Δ_aux_eq_of_isMinimal (R := ℤ_[2]) (K := ℚ_[2])
    (W := C • W) (C₀ * C⁻¹)
  rw [hsmul] at haux
  have hval := congrArg Subtype.val haux
  calc freyTwoAdicMinimalDiscriminantValuation a b
      = freyPadicValuation 2 (C₀ • W).Δ := rfl
    _ = (WeierstrassCurve.valuation_Δ_aux ℤ_[2] (C₀ • W)).val :=
        (freyPadicValuation_eq_valuation_Δ_aux_val (C₀ • W)).symm
    _ = (WeierstrassCurve.valuation_Δ_aux ℤ_[2] (C • W)).val := hval
    _ = freyPadicValuation 2 (C • W).Δ :=
        freyPadicValuation_eq_valuation_Δ_aux_val (C • W)

/-- On a minimal displayed model, `v₂(Δ_min)` is the valuation of the
displayed discriminant. -/
theorem freyTwoAdicMinimalDiscriminantValuation_eq_of_isMinimal (a b : ℕ)
    [hmin : WeierstrassCurve.IsMinimal ℤ_[2] (freyPadicCurve 2 a b)] :
    freyTwoAdicMinimalDiscriminantValuation a b =
      freyPadicValuation 2 (freyPadicCurve 2 a b).Δ := by
  haveI : WeierstrassCurve.IsMinimal ℤ_[2]
      ((1 : WeierstrassCurve.VariableChange ℚ_[2]) • freyPadicCurve 2 a b) := by
    simpa only [one_smul] using hmin
  simpa only [one_smul] using
    freyTwoAdicMinimalDiscriminantValuation_eq_of_variableChange_isMinimal
      (a := a) (b := b) (1 : WeierstrassCurve.VariableChange ℚ_[2])

/-- In the solvable family `b = a + 1 + 4 * m`, `a * b = 16 * n` the halved
model is minimal at `2`, through the unit `c₄ = a² + ab + b²`. -/
theorem freyTwoAdicHalvingModel_isMinimal_of_congruences {a b : ℕ} {m : ℤ} {n : ℕ}
    (hb : (b : ℤ) = (a : ℤ) + 1 + 4 * m) (hab : a * b = 16 * n) :
    WeierstrassCurve.IsMinimal ℤ_[2] (freyTwoAdicHalvingModel a b) := by
  haveI : WeierstrassCurve.IsIntegral ℤ_[2] (freyTwoAdicHalvingModel a b) :=
    freyTwoAdicHalvingModel_isIntegral_of_congruences hb hab
  refine padicWeierstrass_isMinimal_of_c4_valuation_one _ ?_
  rw [freyTwoAdicHalvingModel_c₄]
  exact (freyPadicValuation_two_natCast_eq_one_iff _).mpr
    (two_not_dvd_of_odd (odd_abcInvariantPolynomial_of_int_congruence hb))

/-- `v₂(Δ_min)` in the solvable family: the halved model is the minimal one. -/
theorem freyTwoAdicMinimalDiscriminantValuation_halving_of_congruences {a b : ℕ}
    {m : ℤ} {n : ℕ} (hb : (b : ℤ) = (a : ℤ) + 1 + 4 * m)
    (hab : a * b = 16 * n) :
    freyTwoAdicMinimalDiscriminantValuation a b =
      freyPadicValuation 2 (((n * (a + b)) ^ 2 : ℕ) : ℚ_[2]) := by
  haveI hmin : WeierstrassCurve.IsMinimal ℤ_[2] (freyTwoAdicHalvingModel a b) :=
    freyTwoAdicHalvingModel_isMinimal_of_congruences hb hab
  haveI : WeierstrassCurve.IsMinimal ℤ_[2]
      (freyTwoAdicHalvingChange • freyPadicCurve 2 a b) := hmin
  have h := freyTwoAdicMinimalDiscriminantValuation_eq_of_variableChange_isMinimal
    a b freyTwoAdicHalvingChange
  rw [h]
  change freyPadicValuation 2 (freyTwoAdicHalvingModel a b).Δ = _
  rw [freyTwoAdicHalvingModel_discriminant_of_congruences hab]

/-- Closed form of the solvable-family value: `2 * v₂(n * (a + b))`. -/
theorem freyTwoAdicMinimalDiscriminantValuation_halving_eq_exp_neg {a b : ℕ}
    {m : ℤ} {n : ℕ} (hb : (b : ℤ) = (a : ℤ) + 1 + 4 * m)
    (hab : a * b = 16 * n) (hn : n * (a + b) ≠ 0) :
    freyTwoAdicMinimalDiscriminantValuation a b =
      WithZero.exp (-((2 * padicValNat 2 (n * (a + b)) : ℕ) : ℤ)) := by
  rw [freyTwoAdicMinimalDiscriminantValuation_halving_of_congruences hb hab,
    freyPadicValuation_two_natCast_eq_exp_neg_padicValNat (pow_ne_zero 2 hn),
    padicValNat.pow]

end LeanFormal.IUT
