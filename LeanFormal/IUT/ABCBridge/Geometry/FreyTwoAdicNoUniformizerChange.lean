/-
# The `k = 0` minimality residual of the displayed abc-Frey model at `2`

The parked statement `FreyTwoAdicDisplayedModelNoUniformizerChangeStatement`
(`FreyTwoAdicMinimalityCriterion.lean`) is proved here: on the `k = 0` rows of
the displayed abc-Frey family, no integral variable change of the displayed
model has `u` of 2-adic valuation one.

Proof route.  If an integral change had `u = 2 * U` with `U` a unit of
`ℤ_[2]`, the coefficient formulas of `integralModel ℤ_[2] (C • W)` give
integral elements `R'`, `S'`, `T'` of `ℤ_[2]` with underlying values
`C.r`, `C.s`, `C.t / 4`, and the three exact congruences
`d + 3r - s² ≡ 0 (4)`, `-ab + 2rd + 3r² - 2st ≡ 0 (16)`,
`r(r-a)(r+b) - t² ≡ 0 (32)` hold.  Reducing modulo `32` and applying the
finite residue kernel (`decide`, four parity sub-cases, each verified
exhaustively) yields `4 ∣ b - a - 1 ∧ 16 ∣ ab` or `a ≡ 1 (4) ∧ 16 ∣ a + b`,
contradicting the two `k = 0` hypotheses.

Consequently `FreyTwoAdicDisplayedModelMinimalStatement` holds, and the
additive value card of `FreyTwoAdicAdditiveCaseValueCard.lean` is
unconditional on the `k = 0` rows.

Literature freeze (statement-level): Silverman, *Advanced Topics in the
Arithmetic of Elliptic Curves*, IV.9 and IV.10; Saito 1988 (cited only).
The `m₂` and `swan₂` exponents remain open and are not treated here.
-/

import LeanFormal.IUT.ABCBridge.Geometry.FreyTwoAdicMinimalityCriterion
import Mathlib.NumberTheory.Padics.RingHoms

set_option maxHeartbeats 20000000

noncomputable section

open scoped WeierstrassCurve WithZero

namespace LeanFormal.IUT

/-! ## The finite residue kernel -/

/-- The residue conclusion shared by the four parity sub-kernels: either the
halving congruences `4 ∣ b - a - 1`, `16 ∣ ab` hold, or the `C`-case
congruences `a ≡ 1 (4)`, `16 ∣ a + b` hold. -/
abbrev freyTwoAdicResidueConclusion (A B : ZMod 32) : Prop :=
  ((ZMod.castHom (by norm_num : 4 ∣ 32) (ZMod 4)) (B - A - 1) = 0 ∧
      (ZMod.castHom (by norm_num : 16 ∣ 32) (ZMod 16)) (A * B) = 0) ∨
    ((ZMod.castHom (by norm_num : 4 ∣ 32) (ZMod 4)) (A - 1) = 0 ∧
      (ZMod.castHom (by norm_num : 16 ∣ 32) (ZMod 16)) (A + B) = 0)

/-- A square modulo four only sees the class modulo two. -/
theorem freyTwoAdicZMod4_sq_of_castHom_two (X : ZMod 4) :
    X ^ 2 =
      ((((ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)) X).val : ℕ) : ZMod 4) ^ 2 := by
  decide +revert

/-- `8 * X * Y` modulo sixteen only sees `X` and `Y` modulo two. -/
theorem freyTwoAdicZMod16_eight_mul (X Y : ZMod 32) :
    (ZMod.castHom (by norm_num : 16 ∣ 32) (ZMod 16)) (8 * X * Y) =
      8 * ((((ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2)) X).val : ℕ) : ZMod 16) *
        ((((ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2)) Y).val : ℕ) : ZMod 16) := by
  decide +revert

/-- `16 * X ^ 2` modulo thirty-two only sees `X` modulo two. -/
theorem freyTwoAdicZMod32_sixteen_sq (X : ZMod 32) :
    16 * X ^ 2 =
      16 * (((((ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2)) X).val : ℕ)) : ZMod 32) ^ 2 := by
  decide +revert

/-- Reduction modulo two factors through reduction modulo four. -/
theorem freyTwoAdicZMod2_comp_castHom_four (X : ZMod 32) :
    (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2))
        ((ZMod.castHom (by norm_num : 4 ∣ 32) (ZMod 4)) X) =
      (ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2)) X := by
  decide +revert

/-- The residue kernel, `s` even, `t ≡ 0 (8)` sub-case.  Verified
exhaustively (`32³` cases). -/
theorem freyTwoAdicResidueKernelS0T0 : ∀ (A B R : ZMod 32),
    (ZMod.castHom (by norm_num : 4 ∣ 32) (ZMod 4)) (B - A + 3 * R) = 0 →
    (ZMod.castHom (by norm_num : 16 ∣ 32) (ZMod 16))
        (-(A * B) + 2 * (B - A) * R + 3 * R ^ 2) = 0 →
    R * (R - A) * (R + B) = 0 →
    ¬ ((ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2)) A = 0 ∧
        (ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2)) B = 0) →
    freyTwoAdicResidueConclusion A B := by
  unfold freyTwoAdicResidueConclusion
  decide

/-- The residue kernel, `s` even, `t ≡ 4 (8)` sub-case. -/
theorem freyTwoAdicResidueKernelS0T1 : ∀ (A B R : ZMod 32),
    (ZMod.castHom (by norm_num : 4 ∣ 32) (ZMod 4)) (B - A + 3 * R) = 0 →
    (ZMod.castHom (by norm_num : 16 ∣ 32) (ZMod 16))
        (-(A * B) + 2 * (B - A) * R + 3 * R ^ 2) = 0 →
    R * (R - A) * (R + B) = 16 →
    ¬ ((ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2)) A = 0 ∧
        (ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2)) B = 0) →
    freyTwoAdicResidueConclusion A B := by
  unfold freyTwoAdicResidueConclusion
  decide

/-- The residue kernel, `s` odd, `t ≡ 0 (8)` sub-case. -/
theorem freyTwoAdicResidueKernelS1T0 : ∀ (A B R : ZMod 32),
    (ZMod.castHom (by norm_num : 4 ∣ 32) (ZMod 4)) (B - A + 3 * R) = 1 →
    (ZMod.castHom (by norm_num : 16 ∣ 32) (ZMod 16))
        (-(A * B) + 2 * (B - A) * R + 3 * R ^ 2) = 0 →
    R * (R - A) * (R + B) = 0 →
    ¬ ((ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2)) A = 0 ∧
        (ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2)) B = 0) →
    freyTwoAdicResidueConclusion A B := by
  unfold freyTwoAdicResidueConclusion
  decide

/-- The residue kernel, `s` odd, `t ≡ 4 (8)` sub-case. -/
theorem freyTwoAdicResidueKernelS1T1 : ∀ (A B R : ZMod 32),
    (ZMod.castHom (by norm_num : 4 ∣ 32) (ZMod 4)) (B - A + 3 * R) = 1 →
    (ZMod.castHom (by norm_num : 16 ∣ 32) (ZMod 16))
        (-(A * B) + 2 * (B - A) * R + 3 * R ^ 2) = 8 →
    R * (R - A) * (R + B) = 16 →
    ¬ ((ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2)) A = 0 ∧
        (ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2)) B = 0) →
    freyTwoAdicResidueConclusion A B := by
  unfold freyTwoAdicResidueConclusion
  decide

/-- **The residue kernel.**  For every pair of residues `a`, `b` modulo `32`
with `s ≡ S`, `t ≡ 4 * T2 (mod 8)` the three congruences are unsatisfiable
unless one of the halving/`C`-case conclusions holds.  Assembled from the
four parity sub-kernels. -/
theorem freyTwoAdicResidueKernel : ∀ (A B R : ZMod 32) (S T2 : ZMod 2),
    (ZMod.castHom (by norm_num : 4 ∣ 32) (ZMod 4)) (B - A + 3 * R) =
        (((S.val : ℕ)) : ZMod 4) ^ 2 →
    (ZMod.castHom (by norm_num : 16 ∣ 32) (ZMod 16))
        (-(A * B) + 2 * (B - A) * R + 3 * R ^ 2) =
      8 * ((((S.val : ℕ)) : ZMod 16)) * ((((T2.val : ℕ)) : ZMod 16)) →
    R * (R - A) * (R + B) = 16 * ((((T2.val : ℕ)) : ZMod 32)) ^ 2 →
    ¬ ((ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2)) A = 0 ∧
        (ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2)) B = 0) →
    freyTwoAdicResidueConclusion A B := by
  intro A B R S T2 h1 h2 h3 h4
  fin_cases S <;> fin_cases T2 <;>
    first
      | exact freyTwoAdicResidueKernelS0T0 A B R h1 h2 h3 h4
      | exact freyTwoAdicResidueKernelS0T1 A B R h1 h2 h3 h4
      | exact freyTwoAdicResidueKernelS1T0 A B R h1 h2 h3 h4
      | exact freyTwoAdicResidueKernelS1T1 A B R h1 h2 h3 h4

/-! ## Valuation bridges and the unit extraction -/

/-- For nonzero `z : ℤ_[2]`, the maximal-ideal `intValuation` at `2` is
`exp (-valuation)`. -/
theorem padicInt_two_intValuation_eq_exp_neg_valuation {z : ℤ_[2]} (hz : z ≠ 0) :
    (IsDiscreteValuationRing.maximalIdeal ℤ_[2]).intValuation z =
      WithZero.exp (-((z.valuation : ℕ) : ℤ)) := by
  have hasIdeal : (IsDiscreteValuationRing.maximalIdeal ℤ_[2]).asIdeal =
      Ideal.span {((2 : ℕ) : ℤ_[2])} := by
    rw [show (IsDiscreteValuationRing.maximalIdeal ℤ_[2]).asIdeal =
        IsLocalRing.maximalIdeal ℤ_[2] from rfl]
    exact PadicInt.maximalIdeal_eq_span_p
  have hmem : ∀ m : ℕ,
      (IsDiscreteValuationRing.maximalIdeal ℤ_[2]).intValuation z ≤
        WithZero.exp (-(m : ℤ)) ↔ m ≤ z.valuation := by
    intro m
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem, hasIdeal,
      Ideal.span_singleton_pow]
    exact PadicInt.mem_span_pow_iff_le_valuation z hz m
  have h1 := (hmem z.valuation).mpr le_rfl
  have h2 : ¬ (IsDiscreteValuationRing.maximalIdeal ℤ_[2]).intValuation z ≤
      WithZero.exp (-((z.valuation + 1 : ℕ) : ℤ)) := by
    rw [hmem]
    omega
  have hne : (IsDiscreteValuationRing.maximalIdeal ℤ_[2]).intValuation z ≠ 0 :=
    IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero _ z hz
  have h3 : WithZero.exp (-((z.valuation : ℕ) : ℤ)) ≤
      (IsDiscreteValuationRing.maximalIdeal ℤ_[2]).intValuation z := by
    have hlt := lt_of_not_ge h2
    rw [show (IsDiscreteValuationRing.maximalIdeal ℤ_[2]).intValuation z =
        WithZero.exp ((IsDiscreteValuationRing.maximalIdeal ℤ_[2]).intValuation z).log
        from (WithZero.exp_log hne).symm]
    rw [WithZero.exp_le_exp]
    rw [show (IsDiscreteValuationRing.maximalIdeal ℤ_[2]).intValuation z =
        WithZero.exp ((IsDiscreteValuationRing.maximalIdeal ℤ_[2]).intValuation z).log
        from (WithZero.exp_log hne).symm] at hlt
    rw [WithZero.exp_lt_exp] at hlt
    omega
  exact le_antisymm h1 h3

/-- The DVR valuation used by the reduction predicates on `ℚ_[2]` is
`exp (-Padic.valuation)`. -/
theorem freyPadicValuation_two_eq_exp_neg_padicValuation {x : ℚ_[2]} (hx : x ≠ 0) :
    freyPadicValuation 2 x = WithZero.exp (-(x.valuation : ℤ)) := by
  obtain ⟨aa, bb, hb, hxab⟩ := IsFractionRing.div_surjective ℤ_[2] x
  have hbne : bb ≠ 0 := by
    intro h
    rw [h, map_zero, div_zero] at hxab
    exact hx hxab.symm
  have haane : aa ≠ 0 := by
    intro h
    rw [h, map_zero, zero_div] at hxab
    exact hx hxab.symm
  have hinj := IsFractionRing.injective ℤ_[2] ℚ_[2]
  have haa_alg : (algebraMap ℤ_[2] ℚ_[2] aa) ≠ 0 := fun h => haane (hinj h)
  have hbb_alg : (algebraMap ℤ_[2] ℚ_[2] bb) ≠ 0 := fun h => hbne (hinj h)
  have hφa : freyPadicValuation 2 (algebraMap ℤ_[2] ℚ_[2] aa) =
      WithZero.exp (-((aa.valuation : ℕ) : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact padicInt_two_intValuation_eq_exp_neg_valuation haane
  have hφb : freyPadicValuation 2 (algebraMap ℤ_[2] ℚ_[2] bb) =
      WithZero.exp (-((bb.valuation : ℕ) : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact padicInt_two_intValuation_eq_exp_neg_valuation hbne
  calc freyPadicValuation 2 x
      = freyPadicValuation 2 (algebraMap ℤ_[2] ℚ_[2] aa / algebraMap ℤ_[2] ℚ_[2] bb) := by
        rw [hxab]
    _ = WithZero.exp (-((aa.valuation : ℕ) : ℤ)) *
          (WithZero.exp (-((bb.valuation : ℕ) : ℤ)))⁻¹ := by
        rw [div_eq_mul_inv, map_mul, Valuation.map_inv, hφa, hφb]
    _ = WithZero.exp (((bb.valuation : ℕ) : ℤ) - ((aa.valuation : ℕ) : ℤ)) := by
        rw [← WithZero.exp_neg, ← WithZero.exp_add]
        congr 1
        ring
    _ = WithZero.exp (-(x.valuation : ℤ)) := by
        rw [WithZero.exp_inj, ← hxab, div_eq_mul_inv,
          Padic.valuation_mul haa_alg (inv_ne_zero hbb_alg), Padic.valuation_inv]
        simp only [PadicInt.algebraMap_apply, PadicInt.valuation_coe]
        ring

/-- A rational of DVR value `exp (-1)` is `2` times a unit of `ℤ_[2]`. -/
theorem freyTwoAdic_unit_of_valuation_exp_neg_one {u : ℚ_[2]}
    (hu : freyPadicValuation 2 u = WithZero.exp (-1)) :
    ∃ U : ℤ_[2]ˣ, (U : ℚ_[2]) = u / 2 := by
  have hu_ne : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hu
    exact WithZero.exp_ne_zero hu.symm
  have hval : u.valuation = 1 := by
    have h := freyPadicValuation_two_eq_exp_neg_padicValuation hu_ne
    rw [h, WithZero.exp_inj] at hu
    omega
  have hhalf_val : (u / 2).valuation = 0 := by
    rw [div_eq_mul_inv, Padic.valuation_mul hu_ne (inv_ne_zero (by norm_num)),
      Padic.valuation_inv]
    rw [show (2 : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) from rfl, Padic.valuation_natCast]
    rw [hval, padicValNat_self]
    norm_num
  have hnorm : ‖u / 2‖ = 1 := by
    rw [Padic.norm_eq_zpow_neg_valuation (div_ne_zero hu_ne (by norm_num)), hhalf_val]
    norm_num
  exact ⟨PadicInt.mkUnits hnorm, PadicInt.mkUnits_eq hnorm⟩

/-! ## Coefficient formulas for the variable change -/

/-- The `a₁` coefficient of a general variable change of the displayed Frey
model. -/
theorem freyPadicCurve_variableChange_a₁ (a b : ℕ)
    (C : WeierstrassCurve.VariableChange ℚ_[2]) :
    (C • freyPadicCurve 2 a b).a₁ = C.u⁻¹ * (2 * C.s) := by
  rw [WeierstrassCurve.variableChange_a₁]
  simp only [freyPadicCurve, freyWeierstrassCurve_a₁]
  ring

/-- The `a₂` coefficient of a general variable change of the displayed Frey
model. -/
theorem freyPadicCurve_variableChange_a₂ (a b : ℕ)
    (C : WeierstrassCurve.VariableChange ℚ_[2]) :
    (C • freyPadicCurve 2 a b).a₂ =
      C.u⁻¹ ^ 2 * ((b : ℚ_[2]) - (a : ℚ_[2]) + 3 * C.r - C.s ^ 2) := by
  rw [WeierstrassCurve.variableChange_a₂]
  simp only [freyPadicCurve, freyWeierstrassCurve_a₁, freyWeierstrassCurve_a₂]
  ring

/-- The `a₃` coefficient of a general variable change of the displayed Frey
model. -/
theorem freyPadicCurve_variableChange_a₃ (a b : ℕ)
    (C : WeierstrassCurve.VariableChange ℚ_[2]) :
    (C • freyPadicCurve 2 a b).a₃ = C.u⁻¹ ^ 3 * (2 * C.t) := by
  rw [WeierstrassCurve.variableChange_a₃]
  simp only [freyPadicCurve, freyWeierstrassCurve_a₁, freyWeierstrassCurve_a₃]
  ring

/-- The `a₄` coefficient of a general variable change of the displayed Frey
model. -/
theorem freyPadicCurve_variableChange_a₄ (a b : ℕ)
    (C : WeierstrassCurve.VariableChange ℚ_[2]) :
    (C • freyPadicCurve 2 a b).a₄ =
      C.u⁻¹ ^ 4 * (-((a : ℚ_[2]) * (b : ℚ_[2])) + 2 * C.r * ((b : ℚ_[2]) - (a : ℚ_[2]))
        + 3 * C.r ^ 2 - 2 * C.s * C.t) := by
  rw [WeierstrassCurve.variableChange_a₄]
  simp only [freyPadicCurve, freyWeierstrassCurve_a₁, freyWeierstrassCurve_a₂,
    freyWeierstrassCurve_a₃, freyWeierstrassCurve_a₄]
  ring

/-- The `a₆` coefficient of a general variable change of the displayed Frey
model. -/
theorem freyPadicCurve_variableChange_a₆ (a b : ℕ)
    (C : WeierstrassCurve.VariableChange ℚ_[2]) :
    (C • freyPadicCurve 2 a b).a₆ =
      C.u⁻¹ ^ 6 * (-(C.r * ((a : ℚ_[2]) * (b : ℚ_[2]))) +
        C.r ^ 2 * ((b : ℚ_[2]) - (a : ℚ_[2])) + C.r ^ 3 - C.t ^ 2) := by
  rw [WeierstrassCurve.variableChange_a₆]
  simp only [freyPadicCurve, freyWeierstrassCurve_a₁, freyWeierstrassCurve_a₂,
    freyWeierstrassCurve_a₃, freyWeierstrassCurve_a₄, freyWeierstrassCurve_a₆]
  ring

/-! ## Integer-cast reduction helpers -/

/-- Composition of `castHom` with `toZModPow`. -/
theorem freyTwoAdic_castHom_comp_toZModPow (m n : ℕ) (hmn : m ≤ n) (x : ℤ_[2]) :
    (ZMod.castHom (pow_dvd_pow 2 hmn) (ZMod (2 ^ m)))
        (PadicInt.toZModPow (p := 2) n x) = PadicInt.toZModPow (p := 2) m x := by
  simpa only [RingHom.comp_apply] using
    DFunLike.congr_fun (PadicInt.zmod_cast_comp_toZModPow (p := 2) m n hmn) x

/-- `toZModPow 1` of an integer cast is the class of the integer. -/
theorem freyTwoAdic_toZModPow_one_intCast (n : ℤ) :
    PadicInt.toZModPow (p := 2) 1 ((n : ℤ_[2])) = ((n : ZMod 2)) := by
  simp

/-- `castHom` to `ZMod 4` of an integer cast. -/
theorem freyTwoAdic_castHom_four_intCast (n : ℤ) :
    (ZMod.castHom (by norm_num : 4 ∣ 32) (ZMod 4))
        (PadicInt.toZModPow (p := 2) 5 ((n : ℤ_[2]))) = ((n : ZMod 4)) := by
  rw [show (ZMod.castHom (by norm_num : 4 ∣ 32) (ZMod 4))
      (PadicInt.toZModPow (p := 2) 5 ((n : ℤ_[2]))) =
      PadicInt.toZModPow (p := 2) 2 ((n : ℤ_[2])) from
    freyTwoAdic_castHom_comp_toZModPow 2 5 (by norm_num) ((n : ℤ_[2]))]
  simp

/-- `castHom` to `ZMod 16` of an integer cast. -/
theorem freyTwoAdic_castHom_sixteen_intCast (n : ℤ) :
    (ZMod.castHom (by norm_num : 16 ∣ 32) (ZMod 16))
        (PadicInt.toZModPow (p := 2) 5 ((n : ℤ_[2]))) = ((n : ZMod 16)) := by
  rw [show (ZMod.castHom (by norm_num : 16 ∣ 32) (ZMod 16))
      (PadicInt.toZModPow (p := 2) 5 ((n : ℤ_[2]))) =
      PadicInt.toZModPow (p := 2) 4 ((n : ℤ_[2])) from
    freyTwoAdic_castHom_comp_toZModPow 4 5 (by norm_num) ((n : ℤ_[2]))]
  simp

/-! ## The `k = 0` residue disjunction -/

/-- **The residue disjunction.**  If an integral variable change of the
displayed Frey model has `u` of valuation one, then the halving congruences or
the `C`-case congruences hold. -/
theorem freyTwoAdicK0ResidueDisjunction {a b : ℕ} (htri : IsABCTriple a b (a + b))
    (C : WeierstrassCurve.VariableChange ℚ_[2])
    (hC : WeierstrassCurve.IsIntegral ℤ_[2] (C • freyPadicCurve 2 a b))
    (hval : freyPadicValuation 2 (C.u : ℚ_[2]) = WithZero.exp (-1)) :
    ((4 : ℤ) ∣ (b : ℤ) - (a : ℤ) - 1 ∧ (16 : ℤ) ∣ (a : ℤ) * b) ∨
      (a % 4 = 1 ∧ 16 ∣ a + b) := by
  obtain ⟨U, hU⟩ := freyTwoAdic_unit_of_valuation_exp_neg_one hval
  have hu_eq : (C.u : ℚ_[2]) = 2 * (U : ℚ_[2]) := by
    rw [hU, div_eq_mul_inv]
    rw [← mul_assoc]
    rw [mul_comm (2 : ℚ_[2]) (C.u : ℚ_[2])]
    rw [mul_assoc]
    rw [mul_inv_cancel₀ (by norm_num : (2 : ℚ_[2]) ≠ 0), mul_one]
  have hU_ne : (U : ℚ_[2]) ≠ 0 := fun h =>
    Units.ne_zero U (IsFractionRing.injective ℤ_[2] ℚ_[2] h)
  letI : WeierstrassCurve.IsIntegral ℤ_[2] (C • freyPadicCurve 2 a b) := hC
  set W' := WeierstrassCurve.integralModel ℤ_[2] (C • freyPadicCurve 2 a b) with hW'def
  have hx₁ := WeierstrassCurve.integralModel_a₁_eq (R := ℤ_[2]) (C • freyPadicCurve 2 a b)
  have hx₂ := WeierstrassCurve.integralModel_a₂_eq (R := ℤ_[2]) (C • freyPadicCurve 2 a b)
  have hx₃ := WeierstrassCurve.integralModel_a₃_eq (R := ℤ_[2]) (C • freyPadicCurve 2 a b)
  have hx₄ := WeierstrassCurve.integralModel_a₄_eq (R := ℤ_[2]) (C • freyPadicCurve 2 a b)
  have hx₆ := WeierstrassCurve.integralModel_a₆_eq (R := ℤ_[2]) (C • freyPadicCurve 2 a b)
  have hs_eq : (C.s : ℚ_[2]) = (U : ℚ_[2]) * algebraMap ℤ_[2] ℚ_[2] W'.a₁ := by
    rw [hx₁, freyPadicCurve_variableChange_a₁ a b C, Units.val_inv_eq_inv_val, hu_eq]
    field_simp
  have hS_norm : ‖(C.s : ℚ_[2])‖ ≤ 1 := by
    have hUnorm : ‖(U : ℚ_[2])‖ = 1 := by
      rw [← PadicInt.norm_def (z := (U : ℤ_[2]))]
      exact PadicInt.norm_units U
    rw [hs_eq, norm_mul, hUnorm, one_mul]
    simpa only [PadicInt.algebraMap_apply, PadicInt.norm_def] using
      (PadicInt.norm_le_one W'.a₁)
  let S' : ℤ_[2] := ⟨(C.s : ℚ_[2]), hS_norm⟩
  have ht_eq : (C.t : ℚ_[2]) / 4 =
      (U : ℚ_[2]) ^ 3 * algebraMap ℤ_[2] ℚ_[2] W'.a₃ := by
    rw [hx₃, freyPadicCurve_variableChange_a₃ a b C, Units.val_inv_eq_inv_val, hu_eq]
    field_simp
    ring
  have hT_norm : ‖(C.t : ℚ_[2]) / 4‖ ≤ 1 := by
    have hUnorm : ‖(U : ℚ_[2])‖ = 1 := by
      rw [← PadicInt.norm_def (z := (U : ℤ_[2]))]
      exact PadicInt.norm_units U
    rw [ht_eq, norm_mul, norm_pow, hUnorm, one_pow, one_mul]
    simpa only [PadicInt.algebraMap_apply, PadicInt.norm_def] using
      (PadicInt.norm_le_one W'.a₃)
  let T' : ℤ_[2] := ⟨(C.t : ℚ_[2]) / 4, hT_norm⟩
  have hT4 : (((4 : ℤ_[2]) * T' : ℤ_[2]) : ℚ_[2]) = (C.t : ℚ_[2]) := by
    change (4 : ℚ_[2]) * ((C.t : ℚ_[2]) / 4) = (C.t : ℚ_[2])
    rw [div_eq_mul_inv]
    rw [← mul_assoc]
    rw [mul_comm (4 : ℚ_[2]) (C.t : ℚ_[2])]
    rw [mul_assoc]
    rw [mul_inv_cancel₀ (by norm_num : (4 : ℚ_[2]) ≠ 0), mul_one]
  have h2eq : (b : ℚ_[2]) - (a : ℚ_[2]) + 3 * (C.r : ℚ_[2]) - (C.s : ℚ_[2]) ^ 2 =
      4 * (U : ℚ_[2]) ^ 2 * algebraMap ℤ_[2] ℚ_[2] W'.a₂ := by
    have h2raw : algebraMap ℤ_[2] ℚ_[2] W'.a₂ =
        ((2 : ℚ_[2]) * (U : ℚ_[2]))⁻¹ ^ 2 *
          ((b : ℚ_[2]) - (a : ℚ_[2]) + 3 * (C.r : ℚ_[2]) - (C.s : ℚ_[2]) ^ 2) := by
      rw [hx₂, freyPadicCurve_variableChange_a₂ a b C, Units.val_inv_eq_inv_val, hu_eq]
    rw [h2raw]
    field_simp
    ring
  have hr_eq : 3 * (C.r : ℚ_[2]) =
      4 * (U : ℚ_[2]) ^ 2 * algebraMap ℤ_[2] ℚ_[2] W'.a₂ -
        ((b : ℚ_[2]) - (a : ℚ_[2])) + (C.s : ℚ_[2]) ^ 2 := by
    linear_combination h2eq
  have hR_norm : ‖(C.r : ℚ_[2])‖ ≤ 1 := by
    have h3norm : ‖(3 : ℚ_[2])‖ = 1 := by
      rw [show (3 : ℚ_[2]) = ((3 : ℕ) : ℚ_[2]) from rfl]
      exact Padic.norm_natCast_eq_one_iff.mpr (by decide)
    have hrepr : (C.r : ℚ_[2]) = (3 : ℚ_[2])⁻¹ *
        (4 * (U : ℚ_[2]) ^ 2 * algebraMap ℤ_[2] ℚ_[2] W'.a₂ -
          ((b : ℚ_[2]) - (a : ℚ_[2])) + (C.s : ℚ_[2]) ^ 2) := by
      rw [← hr_eq]
      field_simp
    rw [hrepr, norm_mul, norm_inv, h3norm, inv_one, one_mul]
    have hZ : ‖(4 * (U : ℤ_[2]) ^ 2 * W'.a₂ -
        ((b : ℤ_[2]) - (a : ℤ_[2])) + S' ^ 2 : ℤ_[2])‖ ≤ 1 :=
      PadicInt.norm_le_one _
    have hZq : ‖(((4 * (U : ℤ_[2]) ^ 2 * W'.a₂ -
        ((b : ℤ_[2]) - (a : ℤ_[2])) + S' ^ 2 : ℤ_[2]) : ℚ_[2]))‖ ≤ 1 := by
      simpa only [PadicInt.norm_def] using hZ
    have hpush : (((4 * (U : ℤ_[2]) ^ 2 * W'.a₂ -
        ((b : ℤ_[2]) - (a : ℤ_[2])) + S' ^ 2 : ℤ_[2]) : ℚ_[2])) =
        4 * ((U : ℤ_[2]) : ℚ_[2]) ^ 2 * (W'.a₂ : ℚ_[2]) -
          ((b : ℚ_[2]) - (a : ℚ_[2])) + (C.s : ℚ_[2]) ^ 2 := by
      simp only [PadicInt.coe_add, PadicInt.coe_sub, PadicInt.coe_mul,
        PadicInt.coe_pow, PadicInt.coe_natCast]
      rfl
    rw [hpush] at hZq
    exact hZq
  let R' : ℤ_[2] := ⟨(C.r : ℚ_[2]), hR_norm⟩
  have hE1 : (b : ℤ_[2]) - (a : ℤ_[2]) + 3 * R' - S' ^ 2 =
      4 * ((U : ℤ_[2]) ^ 2 * W'.a₂) := by
    apply IsFractionRing.injective ℤ_[2] ℚ_[2]
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_natCast]
    rw [← mul_assoc]
    exact h2eq
  have h4eq : -((a : ℚ_[2]) * (b : ℚ_[2])) + 2 * (C.r : ℚ_[2]) * ((b : ℚ_[2]) - (a : ℚ_[2]))
      + 3 * (C.r : ℚ_[2]) ^ 2 - 2 * (C.s : ℚ_[2]) * (C.t : ℚ_[2]) =
      16 * (U : ℚ_[2]) ^ 4 * algebraMap ℤ_[2] ℚ_[2] W'.a₄ := by
    have h4raw : algebraMap ℤ_[2] ℚ_[2] W'.a₄ =
        ((2 : ℚ_[2]) * (U : ℚ_[2]))⁻¹ ^ 4 *
          (-((a : ℚ_[2]) * (b : ℚ_[2])) + 2 * (C.r : ℚ_[2]) * ((b : ℚ_[2]) - (a : ℚ_[2]))
            + 3 * (C.r : ℚ_[2]) ^ 2 - 2 * (C.s : ℚ_[2]) * (C.t : ℚ_[2])) := by
      rw [hx₄, freyPadicCurve_variableChange_a₄ a b C, Units.val_inv_eq_inv_val, hu_eq]
    rw [h4raw]
    field_simp
    ring
  have hE4 : -((a : ℤ_[2]) * (b : ℤ_[2])) + 2 * R' * ((b : ℤ_[2]) - (a : ℤ_[2]))
      + 3 * R' ^ 2 - 2 * S' * (4 * T') = 16 * ((U : ℤ_[2]) ^ 4 * W'.a₄) := by
    apply IsFractionRing.injective ℤ_[2] ℚ_[2]
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_natCast, map_neg]
    have hT4q : (4 : ℚ_[2]) * (algebraMap ℤ_[2] ℚ_[2] T') = (C.t : ℚ_[2]) := hT4
    rw [hT4q]
    rw [← mul_assoc]
    exact h4eq
  have h6eq : (C.r : ℚ_[2]) * ((C.r : ℚ_[2]) - (a : ℚ_[2])) * ((C.r : ℚ_[2]) + (b : ℚ_[2])) -
      (C.t : ℚ_[2]) ^ 2 = 64 * (U : ℚ_[2]) ^ 6 * algebraMap ℤ_[2] ℚ_[2] W'.a₆ := by
    have h6raw : algebraMap ℤ_[2] ℚ_[2] W'.a₆ =
        ((2 : ℚ_[2]) * (U : ℚ_[2]))⁻¹ ^ 6 *
          (-((C.r : ℚ_[2]) * ((a : ℚ_[2]) * (b : ℚ_[2]))) +
            (C.r : ℚ_[2]) ^ 2 * ((b : ℚ_[2]) - (a : ℚ_[2])) + (C.r : ℚ_[2]) ^ 3 -
              (C.t : ℚ_[2]) ^ 2) := by
      rw [hx₆, freyPadicCurve_variableChange_a₆ a b C, Units.val_inv_eq_inv_val, hu_eq]
    rw [h6raw]
    field_simp
    ring
  have hE6 : R' * (R' - (a : ℤ_[2])) * (R' + (b : ℤ_[2])) - (4 * T') ^ 2 =
      64 * ((U : ℤ_[2]) ^ 6 * W'.a₆) := by
    apply IsFractionRing.injective ℤ_[2] ℚ_[2]
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_natCast]
    have hT4q : (4 : ℚ_[2]) * (algebraMap ℤ_[2] ℚ_[2] T') = (C.t : ℚ_[2]) := hT4
    rw [hT4q]
    rw [← mul_assoc]
    exact h6eq
  have h1z : PadicInt.toZModPow (p := 2) 2
      ((b : ℤ_[2]) - (a : ℤ_[2]) + 3 * R' - S' ^ 2) = 0 := by
    rw [hE1]
    have hmem : (4 : ℤ_[2]) * ((U : ℤ_[2]) ^ 2 * W'.a₂) ∈
        RingHom.ker (PadicInt.toZModPow (p := 2) 2) := by
      rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
      exact ⟨(U : ℤ_[2]) ^ 2 * W'.a₂, by rw [show (((2 : ℕ) : ℤ_[2]) ^ 2) = 4 by norm_num]⟩
    exact RingHom.mem_ker.mp hmem
  have h4z : PadicInt.toZModPow (p := 2) 4
      (-((a : ℤ_[2]) * (b : ℤ_[2])) + 2 * R' * ((b : ℤ_[2]) - (a : ℤ_[2]))
        + 3 * R' ^ 2 - 2 * S' * (4 * T')) = 0 := by
    rw [hE4]
    have hmem : (16 : ℤ_[2]) * ((U : ℤ_[2]) ^ 4 * W'.a₄) ∈
        RingHom.ker (PadicInt.toZModPow (p := 2) 4) := by
      rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
      exact ⟨(U : ℤ_[2]) ^ 4 * W'.a₄, by rw [show (((2 : ℕ) : ℤ_[2]) ^ 4) = 16 by norm_num]⟩
    exact RingHom.mem_ker.mp hmem
  have h6z : PadicInt.toZModPow (p := 2) 6
      (R' * (R' - (a : ℤ_[2])) * (R' + (b : ℤ_[2])) - (4 * T') ^ 2) = 0 := by
    rw [hE6]
    have hmem : (64 : ℤ_[2]) * ((U : ℤ_[2]) ^ 6 * W'.a₆) ∈
        RingHom.ker (PadicInt.toZModPow (p := 2) 6) := by
      rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
      exact ⟨(U : ℤ_[2]) ^ 6 * W'.a₆, by rw [show (((2 : ℕ) : ℤ_[2]) ^ 6) = 64 by norm_num]⟩
    exact RingHom.mem_ker.mp hmem
  set A : ZMod 32 := PadicInt.toZModPow (p := 2) 5 ((a : ℤ_[2])) with hA
  set B : ZMod 32 := PadicInt.toZModPow (p := 2) 5 ((b : ℤ_[2])) with hB
  set R : ZMod 32 := PadicInt.toZModPow (p := 2) 5 R' with hR
  set P : ZMod 32 := PadicInt.toZModPow (p := 2) 5 S' with hP
  set Q : ZMod 32 := PadicInt.toZModPow (p := 2) 5 T' with hQ
  have h5A : PadicInt.toZModPow (p := 2) 5 ((a : ℤ_[2])) = A := hA.symm
  have h5B : PadicInt.toZModPow (p := 2) 5 ((b : ℤ_[2])) = B := hB.symm
  have h5R' : PadicInt.toZModPow (p := 2) 5 R' = R := hR.symm
  have h5P : PadicInt.toZModPow (p := 2) 5 S' = P := hP.symm
  have h5Q : PadicInt.toZModPow (p := 2) 5 T' = Q := hQ.symm
  have hθ1 : PadicInt.toZModPow (p := 2) 5
      ((b : ℤ_[2]) - (a : ℤ_[2]) + 3 * R' - S' ^ 2) =
      (B - A) + 3 * R - P ^ 2 := by
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
    rw [h5A, h5B, h5R', h5P]
  have hθ4 : PadicInt.toZModPow (p := 2) 5
      (-((a : ℤ_[2]) * (b : ℤ_[2])) + 2 * R' * ((b : ℤ_[2]) - (a : ℤ_[2]))
        + 3 * R' ^ 2 - 2 * S' * (4 * T')) =
      (-(A * B) + 2 * (B - A) * R + 3 * R ^ 2) - 8 * P * Q := by
    simp only [map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat]
    rw [h5A, h5B, h5R', h5P, h5Q]; ring
  have hθ5 : PadicInt.toZModPow (p := 2) 5
      (R' * (R' - (a : ℤ_[2])) * (R' + (b : ℤ_[2])) - (4 * T') ^ 2) =
      R * (R - A) * (R + B) - 16 * Q ^ 2 := by
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
    rw [h5A, h5B, h5R', h5Q]; ring
  have h1k : (ZMod.castHom (by norm_num : 4 ∣ 32) (ZMod 4)) (B - A + 3 * R) =
      ((((ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2))
        (PadicInt.toZModPow (p := 2) 5 S')).val : ℕ) : ZMod 4) ^ 2 := by
    have h0 : (ZMod.castHom (by norm_num : 4 ∣ 32) (ZMod 4))
        ((B - A) + 3 * R - P ^ 2) = 0 := by
      rw [← hθ1]
      exact (freyTwoAdic_castHom_comp_toZModPow 2 5 (by norm_num)
        ((b : ℤ_[2]) - (a : ℤ_[2]) + 3 * R' - S' ^ 2)).trans h1z
    rw [map_sub, sub_eq_zero] at h0
    have hP2 : (ZMod.castHom (by norm_num : 4 ∣ 32) (ZMod 4)) (P ^ 2) =
        ((((ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2))
          (PadicInt.toZModPow (p := 2) 5 S')).val : ℕ) : ZMod 4) ^ 2 := by
      rw [map_pow]
      rw [show (ZMod.castHom (by norm_num : 4 ∣ 32) (ZMod 4)) P =
          (ZMod.castHom (by norm_num : 4 ∣ 32) (ZMod 4))
            (PadicInt.toZModPow (p := 2) 5 S') from by rw [← h5P]]
      rw [show (ZMod.castHom (by norm_num : 4 ∣ 32) (ZMod 4))
            (PadicInt.toZModPow (p := 2) 5 S') =
          PadicInt.toZModPow (p := 2) 2 S' from
        freyTwoAdic_castHom_comp_toZModPow 2 5 (by norm_num) S']
      rw [freyTwoAdicZMod4_sq_of_castHom_two (PadicInt.toZModPow (p := 2) 2 S')]
      rw [show (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2))
            (PadicInt.toZModPow (p := 2) 2 S') =
          (ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2))
            (PadicInt.toZModPow (p := 2) 5 S') from by
        rw [← freyTwoAdic_castHom_comp_toZModPow 2 5 (by norm_num) S']
        exact freyTwoAdicZMod2_comp_castHom_four _]
    exact h0.trans hP2
  have h2k : (ZMod.castHom (by norm_num : 16 ∣ 32) (ZMod 16))
      (-(A * B) + 2 * (B - A) * R + 3 * R ^ 2) =
      8 * ((((ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2))
        (PadicInt.toZModPow (p := 2) 5 S')).val : ℕ) : ZMod 16) *
        ((((ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2))
          (PadicInt.toZModPow (p := 2) 5 T')).val : ℕ) : ZMod 16) := by
    have h0 : (ZMod.castHom (by norm_num : 16 ∣ 32) (ZMod 16))
        ((-(A * B) + 2 * (B - A) * R + 3 * R ^ 2) - 8 * P * Q) = 0 := by
      rw [← hθ4]
      exact (freyTwoAdic_castHom_comp_toZModPow 4 5 (by norm_num)
        (-((a : ℤ_[2]) * (b : ℤ_[2])) + 2 * R' * ((b : ℤ_[2]) - (a : ℤ_[2]))
          + 3 * R' ^ 2 - 2 * S' * (4 * T'))).trans h4z
    rw [map_sub, sub_eq_zero] at h0
    rw [h0, freyTwoAdicZMod16_eight_mul]
  have h3k : R * (R - A) * (R + B) =
      16 * ((((ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2))
        (PadicInt.toZModPow (p := 2) 5 T')).val : ℕ) : ZMod 32) ^ 2 := by
    have h0 : PadicInt.toZModPow (p := 2) 5
        (R' * (R' - (a : ℤ_[2])) * (R' + (b : ℤ_[2])) - (4 * T') ^ 2) = 0 := by
      have hc := freyTwoAdic_castHom_comp_toZModPow 5 6 (by norm_num)
        (R' * (R' - (a : ℤ_[2])) * (R' + (b : ℤ_[2])) - (4 * T') ^ 2)
      rw [h6z, map_zero] at hc
      exact hc.symm
    rw [hθ5] at h0
    have hR1 : R * (R - A) * (R + B) = 16 * Q ^ 2 := sub_eq_zero.mp h0
    rw [hR1, ← h5Q]
    exact freyTwoAdicZMod32_sixteen_sq (PadicInt.toZModPow (p := 2) 5 T')
  have h4k : ¬ ((ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2)) A = 0 ∧
      (ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2)) B = 0) := by
    rintro ⟨hA0, hB0⟩
    have h2a : (2 : ℤ) ∣ (a : ℤ) := by
      have hc : (ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2))
          (PadicInt.toZModPow (p := 2) 5 ((a : ℤ_[2]))) = 0 := by
        simpa only [← h5A] using hA0
      have hc1 : PadicInt.toZModPow (p := 2) 1 ((a : ℤ_[2])) = 0 :=
        (freyTwoAdic_castHom_comp_toZModPow 1 5 (by norm_num) ((a : ℤ_[2]))).symm.trans hc
      have hc1' : PadicInt.toZModPow (p := 2) 1 (((a : ℤ)) : ℤ_[2]) = 0 := by
        rw [show ((a : ℤ_[2])) = (((a : ℤ)) : ℤ_[2]) from by rw [Int.cast_natCast]] at hc1
        exact hc1
      have hc2 : (((a : ℤ)) : ZMod 2) = 0 := by
        rw [← freyTwoAdic_toZModPow_one_intCast ((a : ℤ))]
        exact hc1'
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd ((a : ℤ)) 2).mp hc2
    have h2b : (2 : ℤ) ∣ (b : ℤ) := by
      have hc : (ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2))
          (PadicInt.toZModPow (p := 2) 5 ((b : ℤ_[2]))) = 0 := by
        simpa only [← h5B] using hB0
      have hc1 : PadicInt.toZModPow (p := 2) 1 ((b : ℤ_[2])) = 0 :=
        (freyTwoAdic_castHom_comp_toZModPow 1 5 (by norm_num) ((b : ℤ_[2]))).symm.trans hc
      have hc1' : PadicInt.toZModPow (p := 2) 1 (((b : ℤ)) : ℤ_[2]) = 0 := by
        rw [show ((b : ℤ_[2])) = (((b : ℤ)) : ℤ_[2]) from by rw [Int.cast_natCast]] at hc1
        exact hc1
      have hc2 : (((b : ℤ)) : ZMod 2) = 0 := by
        rw [← freyTwoAdic_toZModPow_one_intCast ((b : ℤ))]
        exact hc1'
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd ((b : ℤ)) 2).mp hc2
    have h2na : 2 ∣ a := Int.natCast_dvd_natCast.mp h2a
    have h2nb : 2 ∣ b := Int.natCast_dvd_natCast.mp h2b
    have h2g : 2 ∣ a.gcd b := Nat.dvd_gcd h2na h2nb
    have hcop : Nat.Coprime a b := htri.2.2.2
    rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at h2g
    exact absurd h2g (by norm_num)
  have hker : freyTwoAdicResidueConclusion A B :=
    freyTwoAdicResidueKernel A B R
      ((ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2))
        (PadicInt.toZModPow (p := 2) 5 S'))
      ((ZMod.castHom (by norm_num : 2 ∣ 32) (ZMod 2))
        (PadicInt.toZModPow (p := 2) 5 T'))
      h1k h2k h3k h4k
  rcases hker with ⟨h1, h2⟩ | ⟨h3, h4⟩
  · left
    refine ⟨?_, ?_⟩
    · have hBm : B - A - 1 =
          PadicInt.toZModPow (p := 2) 5 ((((b : ℤ) - (a : ℤ) - 1 : ℤ)) : ℤ_[2]) := by
        rw [← h5B, ← h5A, ← map_sub, ← map_one (PadicInt.toZModPow (p := 2) 5), ← map_sub]
        congr 1; push_cast; ring
      have h1' : (ZMod.castHom (by norm_num : 4 ∣ 32) (ZMod 4))
          (PadicInt.toZModPow (p := 2) 5
            ((((b : ℤ) - (a : ℤ) - 1 : ℤ)) : ℤ_[2])) = 0 := by
        rw [← hBm]
        exact h1
      have h1'' : ((((b : ℤ) - (a : ℤ) - 1 : ℤ)) : ZMod 4) = 0 := by
        rw [← freyTwoAdic_castHom_four_intCast ((b : ℤ) - (a : ℤ) - 1)]
        exact h1'
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd ((b : ℤ) - (a : ℤ) - 1) 4).mp h1''
    · have hABm : A * B =
          PadicInt.toZModPow (p := 2) 5 ((((a : ℤ) * (b : ℤ) : ℤ)) : ℤ_[2]) := by
        rw [← h5A, ← h5B, ← map_mul]
        congr 1; push_cast; ring
      have h2' : (ZMod.castHom (by norm_num : 16 ∣ 32) (ZMod 16))
          (PadicInt.toZModPow (p := 2) 5 ((((a : ℤ) * (b : ℤ) : ℤ)) : ℤ_[2])) = 0 := by
        rw [← hABm]
        exact h2
      have h2'' : ((((a : ℤ) * (b : ℤ) : ℤ)) : ZMod 16) = 0 := by
        rw [← freyTwoAdic_castHom_sixteen_intCast ((a : ℤ) * (b : ℤ))]
        exact h2'
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd ((a : ℤ) * (b : ℤ)) 16).mp h2''
  · right
    refine ⟨?_, ?_⟩
    · have hA1 : A - 1 =
          PadicInt.toZModPow (p := 2) 5 ((((a : ℤ) - 1 : ℤ)) : ℤ_[2]) := by
        rw [← h5A, ← map_one (PadicInt.toZModPow (p := 2) 5), ← map_sub]
        congr 1; push_cast; ring
      have h3' : (ZMod.castHom (by norm_num : 4 ∣ 32) (ZMod 4))
          (PadicInt.toZModPow (p := 2) 5 ((((a : ℤ) - 1 : ℤ)) : ℤ_[2])) = 0 := by
        rw [← hA1]
        exact h3
      have h3'' : ((((a : ℤ) - 1 : ℤ)) : ZMod 4) = 0 := by
        rw [← freyTwoAdic_castHom_four_intCast ((a : ℤ) - 1)]
        exact h3'
      have hcz : (a : ZMod 4) = 1 := by
        have h := h3''
        push_cast at h
        exact sub_eq_zero.mp h
      have hv := congrArg ZMod.val hcz
      rw [ZMod.val_natCast] at hv
      rw [ZMod.val_one_eq_one_mod 4] at hv
      norm_num at hv
      exact hv
    · have hAB2 : A + B =
          PadicInt.toZModPow (p := 2) 5 ((((a : ℤ) + (b : ℤ) : ℤ)) : ℤ_[2]) := by
        rw [← h5A, ← h5B, ← map_add]
        congr 1; push_cast; ring
      have h4' : (ZMod.castHom (by norm_num : 16 ∣ 32) (ZMod 16))
          (PadicInt.toZModPow (p := 2) 5 ((((a : ℤ) + (b : ℤ) : ℤ)) : ℤ_[2])) = 0 := by
        rw [← hAB2]
        exact h4
      have h4'' : ((((a : ℤ) + (b : ℤ) : ℤ)) : ZMod 16) = 0 := by
        rw [← freyTwoAdic_castHom_sixteen_intCast ((a : ℤ) + (b : ℤ))]
        exact h4'
      have hz : (16 : ℤ) ∣ (a : ℤ) + (b : ℤ) :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd ((a : ℤ) + (b : ℤ)) 16).mp h4''
      have hz' : (16 : ℤ) ∣ (((a + b : ℕ)) : ℤ) := by
        push_cast
        exact hz
      exact Int.natCast_dvd_natCast.mp hz'

/-! ## The `k = 0` residual theorem -/

/-- **The `k = 0` residual is proved.**  No integral variable change of the
displayed abc-Frey model at `2` has `u` of valuation one. -/
theorem freyTwoAdicDisplayedModelNoUniformizerChange :
    FreyTwoAdicDisplayedModelNoUniformizerChangeStatement := by
  intro a b htri hhalving hcaseC C hC hval
  rcases freyTwoAdicK0ResidueDisjunction htri C hC hval with h | h
  · exact hhalving h
  · exact hcaseC h

/-- The displayed model is minimal on the `k = 0` rows: the connector applied
to the proved residual. -/
theorem freyTwoAdicDisplayedModelMinimal_proved :
    FreyTwoAdicDisplayedModelMinimalStatement :=
  freyTwoAdicDisplayedModelMinimal_of_noUniformizerChange
    freyTwoAdicDisplayedModelNoUniformizerChange

/-- **The additive value card at `2`, de-conditioned on the `k = 0` rows**:
for ABC triples satisfying the two `k = 0` hypotheses, the minimality
hypothesis of `freyTwoAdicAdditiveCaseValueCard` is discharged by
`freyTwoAdicDisplayedModelMinimal_proved`. -/
theorem freyTwoAdicAdditiveCaseValueCard_k0 {a b : ℕ} (htri : IsABCTriple a b (a + b))
    (hhalving : ¬ ((4 : ℤ) ∣ (b : ℤ) - (a : ℤ) - 1 ∧ (16 : ℤ) ∣ (a : ℤ) * b))
    (hcaseC : ¬ (a % 4 = 1 ∧ 16 ∣ a + b)) :
    WeierstrassCurve.HasAdditiveReduction ℤ_[2] (freyPadicCurve 2 a b) ∧
      freyTwoAdicMinimalDiscriminantValuation a b =
        WithZero.exp (-((4 + 2 * padicValNat 2 (a * b * (a + b)) : ℕ) : ℤ)) ∧
      freyPadicValuation 2 (freyPadicCurve 2 a b).c₄ = WithZero.exp (-4) := by
  have hmin : WeierstrassCurve.IsMinimal ℤ_[2] (freyPadicCurve 2 a b) :=
    freyTwoAdicDisplayedModelMinimal_proved a b htri hhalving hcaseC
  letI : WeierstrassCurve.IsMinimal ℤ_[2] (freyPadicCurve 2 a b) := hmin
  exact freyTwoAdicAdditiveCaseValueCard a b htri

end LeanFormal.IUT
