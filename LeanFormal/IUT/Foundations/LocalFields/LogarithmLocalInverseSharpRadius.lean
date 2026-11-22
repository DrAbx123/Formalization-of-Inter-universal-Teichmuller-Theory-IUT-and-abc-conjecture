import LeanFormal.IUT.Foundations.LocalFields.LogarithmRemainder
import LeanFormal.IUT.Foundations.LocalFields.LogarithmLocalInverse
import LeanFormal.IUT.Foundations.LocalFields.UnscaledUnitLogLattice
import LeanFormal.IUT.Foundations.LocalFields.PadicFractionalLattice
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Sharp radius for the local logarithm inverse

The elementary remainder estimate in `LogarithmRemainder` has contraction
constant `2r` and therefore gives an inverse only on `r < 1/2`.  Using the
exact p-adic size of the denominators, the tail term at index `n` has size
at most `(r * p ^ (1 / (p - 1))) ^ (n + 1)`.  The resulting contraction
constant is `r * p ^ (1 / (p - 1))`, so the inverse exists on the full
open radius `r < p ^ (-1 / (p - 1))`.

The last theorem is the consumer needed for general fractional lattices:
for `a > 1 / (p - 1)`, the norm ball `p ^ (-a)` lies in the actual
unscaled unit-log lattice.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open Filter
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NNReal Topology

noncomputable section

section PadicDenominator

variable {p : ℕ} [Fact p.Prime]

/-- The exact p-adic size of a nonzero integer denominator. -/
theorem padicLog_denom_norm_inv_eq_rpow_padicValNat {k : ℕ} (hk : k ≠ 0) :
    ‖(k : ℚ_[p])‖⁻¹ = (p : ℝ) ^ (padicValNat p k) := by
  have hne : (k : ℚ_[p]) ≠ 0 := by
    exact_mod_cast hk
  have hnorm : ‖(k : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p k : ℤ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hne, Padic.valuation_natCast]
  rw [hnorm, (inv_zpow (p : ℝ) (-(padicValNat p k : ℤ))).symm, inv_zpow',
    neg_neg, zpow_natCast]

/-- The exponent of the p-part of `k` is at most `(k - 1) / (p - 1)`. -/
theorem padicValNat_cast_le_div_prime_sub_one {k : ℕ} (hk : 2 ≤ k) :
    (padicValNat p k : ℝ) ≤ ((k : ℝ) - 1) / ((p : ℝ) - 1) := by
  let v := padicValNat p k
  have hk0 : k ≠ 0 := by omega
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp_sub_pos : 0 < (p : ℝ) - 1 := by linarith
  have hpow_le : (p : ℝ) ^ v ≤ (k : ℝ) := by
    have hdiv : p ^ v ∣ k := pow_padicValNat_dvd
    have hle : p ^ v ≤ k := Nat.le_of_dvd (by omega) hdiv
    exact_mod_cast hle
  have hbern : (v : ℝ) * ((p : ℝ) - 1) ≤ (p : ℝ) ^ v - 1 := by
    have h := one_add_mul_le_pow (a := (p : ℝ) - 1) (by linarith) v
    have hp_eq : 1 + ((p : ℝ) - 1) = (p : ℝ) := by ring
    rw [hp_eq] at h
    linarith
  have hcombined : (v : ℝ) * ((p : ℝ) - 1) ≤ (k : ℝ) - 1 := by
    linarith
  exact (le_div_iff₀ hp_sub_pos).mpr hcombined

end PadicDenominator

section LocalField

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]

include localNormedAlgebra

omit [CharZero K] [CompleteSpace K] [IsUltrametricDist K] in
/-- The exact denominator size transported to the local field. -/
theorem localLog_denom_norm_inv_eq_rpow_padicValNat {k : ℕ} (hk : k ≠ 0) :
    ‖(k : K)‖⁻¹ = (p : ℝ) ^ (padicValNat p k) := by
  have heq : ‖(k : K)‖ = ‖(k : ℚ_[p])‖ := by
    simpa only [map_natCast] using norm_algebraMap' K (k : ℚ_[p])
  rw [heq]
  exact padicLog_denom_norm_inv_eq_rpow_padicValNat (p := p) hk

omit [CharZero K] [CompleteSpace K] [IsUltrametricDist K] in
/-- Sharp denominator bound by the fractional prime power. -/
theorem localLog_denom_norm_inv_le_sharp_rpow {k : ℕ} (hk : 2 ≤ k) :
    ‖(k : K)‖⁻¹ ≤ (p : ℝ) ^ (((k : ℝ) - 1) / ((p : ℝ) - 1)) := by
  rw [localLog_denom_norm_inv_eq_rpow_padicValNat (K := K) (p := p) (by omega)]
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le
    (show (1 : ℝ) ≤ (p : ℝ) by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
    (padicValNat_cast_le_div_prime_sub_one (p := p) hk)

omit [CharZero K] [CompleteSpace K] in
/-- A sharp termwise estimate for the nonlinear remainder.  At index `n`
the denominator is `n + 2`, whose p-adic inverse norm is at most
`p ^ ((n + 1) / (p - 1))`. -/
theorem norm_logRemainderTerm_sub_le_sharp
    (x y : K) (n : ℕ) (r : ℝ)
    (hr0 : 0 ≤ r)
    (hrsharp : r * (p : ℝ) ^ (1 / ((p : ℝ) - 1)) ≤ 1)
    (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖logRemainderTerm x n - logRemainderTerm y n‖ ≤
      (r * (p : ℝ) ^ (1 / ((p : ℝ) - 1))) * ‖x - y‖ := by
  have heq : logRemainderTerm x n - logRemainderTerm y n =
      -((-1 : K) ^ (n + 1 + 1) *
        (x ^ (n + 1 + 1) - y ^ (n + 1 + 1)) / (n + 1 + 1 : K)) := by
    simp only [logRemainderTerm, negativeLogTerm, Nat.cast_add, Nat.cast_one]
    ring
  rw [heq, norm_neg, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, div_eq_mul_inv]
  have hden : ‖((n : K) + 1 + 1)‖⁻¹ ≤
      (p : ℝ) ^ (((n : ℝ) + 1) / ((p : ℝ) - 1)) := by
    have harg : ((n + 2 : ℕ) : ℝ) - 1 = (n : ℝ) + 1 := by
      push_cast
      ring
    have h := localLog_denom_norm_inv_le_sharp_rpow (K := K) (p := p)
      (k := n + 2) (by omega)
    rw [harg] at h
    push_cast at h
    have hshift : (n : K) + 2 = (n : K) + 1 + 1 := by ring
    simpa only [hshift] using h
  have hp_nonneg : 0 ≤ (p : ℝ) := by positivity
  calc
    _ ≤ (‖x - y‖ * r ^ (n + 1)) * ‖((n : K) + 1 + 1)‖⁻¹ := by
        exact mul_le_mul_of_nonneg_right
          (norm_power_difference_le x y hr0 hx hy (n + 1))
          (inv_nonneg.mpr (norm_nonneg ((n : K) + 1 + 1)))
    _ ≤ (‖x - y‖ * r ^ (n + 1)) *
          (p : ℝ) ^ (((n : ℝ) + 1) / ((p : ℝ) - 1)) := by
        exact mul_le_mul_of_nonneg_left hden (by positivity)
    _ = ‖x - y‖ * (r * (p : ℝ) ^ (1 / ((p : ℝ) - 1))) ^ (n + 1) := by
        rw [show (p : ℝ) ^ (((n : ℝ) + 1) / ((p : ℝ) - 1)) =
            ((p : ℝ) ^ (1 / ((p : ℝ) - 1))) ^ (n + 1) by
          rw [show ((n : ℝ) + 1) / ((p : ℝ) - 1) =
              (1 / ((p : ℝ) - 1)) * ((n : ℝ) + 1) by ring]
          simpa only [Nat.cast_add, Nat.cast_one] using
            (Real.rpow_mul_natCast hp_nonneg (1 / ((p : ℝ) - 1)) (n + 1))]
        rw [mul_pow]
        ring
    _ ≤ ‖x - y‖ * (r * (p : ℝ) ^ (1 / ((p : ℝ) - 1))) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact pow_le_of_le_one (mul_nonneg hr0 (Real.rpow_nonneg hp_nonneg _)) hrsharp
          (Nat.succ_ne_zero n)
    _ = (r * (p : ℝ) ^ (1 / ((p : ℝ) - 1))) * ‖x - y‖ := by ring

/-- The actual logarithmic remainder contracts with the sharp constant. -/
theorem norm_logRemainder_sub_le_sharp
    (x y : K) (r : ℝ)
    (hr0 : 0 ≤ r)
    (hrsharp : r * (p : ℝ) ^ (1 / ((p : ℝ) - 1)) ≤ 1)
    (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖logRemainder x - logRemainder y‖ ≤
      (r * (p : ℝ) ^ (1 / ((p : ℝ) - 1))) * ‖x - y‖ := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  have hqpos : 0 < (p : ℝ) ^ (1 / ((p : ℝ) - 1)) := by
    exact Real.rpow_pos_of_pos (by positivity) _
  have hqgt : 1 < (p : ℝ) ^ (1 / ((p : ℝ) - 1)) := by
    exact Real.one_lt_rpow hp1 (by positivity)
  have hrone : r < 1 := by
    by_contra hnot
    have hrge : 1 ≤ r := le_of_not_gt hnot
    have hqle : (p : ℝ) ^ (1 / ((p : ℝ) - 1)) ≤
        r * (p : ℝ) ^ (1 / ((p : ℝ) - 1)) := by
      calc
        (p : ℝ) ^ (1 / ((p : ℝ) - 1)) = 1 * (p : ℝ) ^ (1 / ((p : ℝ) - 1)) := by
          ring
        _ ≤ r * (p : ℝ) ^ (1 / ((p : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_right hrge hqpos.le
    linarith
  have hs := (logRemainder_hasSum (p := p) x (hx.trans_lt hrone)).sub
    (logRemainder_hasSum (p := p) y (hy.trans_lt hrone))
  have ht := (continuous_norm.tendsto _).comp hs.tendsto_sum_nat
  apply le_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro n
  exact norm_finsetSum_le_of_le_max _ (Finset.range n) (by positivity)
    (fun i _ => norm_logRemainderTerm_sub_le_sharp (p := p) x y i r hr0 hrsharp hx hy)

/-- Sharp local inverse of `log1p` on the full open radius
`p ^ (-1 / (p - 1))`. -/
theorem exists_log1p_preimage_sharp {r : ℝ} (hr : 0 ≤ r)
    (hrsharp : r < (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))))
    {y : K} (hy : ‖y‖ ≤ r) :
    ∃ x : K, ‖x‖ ≤ r ∧ log1p x = y := by
  let q : ℝ := (p : ℝ) ^ (1 / ((p : ℝ) - 1))
  let cReal : ℝ := r * q
  have hp_pos : 0 < (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have hq_pos : 0 < q := by
    exact Real.rpow_pos_of_pos hp_pos _
  have hc0 : 0 ≤ cReal := mul_nonneg hr hq_pos.le
  have hc_lt : cReal < 1 := by
    have hmul := mul_lt_mul_of_pos_right hrsharp hq_pos
    have hprod : (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) * q = 1 := by
      dsimp [q]
      rw [← Real.rpow_add hp_pos]
      simp
    change r * q < 1
    exact hmul.trans_eq hprod
  let B := {x : K // ‖x‖ ≤ r}
  have hclosed : IsClosed {x : K | ‖x‖ ≤ r} :=
    isClosed_le continuous_norm continuous_const
  letI : CompleteSpace B := hclosed.isComplete.completeSpace_coe
  letI : Nonempty B := ⟨⟨0, by simpa using hr⟩⟩
  have hzero : logRemainder (0 : K) = 0 := by simp [logRemainder, log1p_zero]
  have hrem : ∀ x : B, ‖logRemainder (x : K)‖ ≤ r := by
    intro x
    have h := norm_logRemainder_sub_le_sharp (p := p) (x : K) 0 r hr hc_lt.le
      x.property (by simpa using hr)
    rw [hzero, sub_zero, sub_zero] at h
    exact h.trans ((mul_le_of_le_one_left (norm_nonneg _) hc_lt.le).trans x.property)
  let F : B → B := fun x => ⟨y - logRemainder (x : K), by
    apply le_trans _ (max_le hy (hrem x))
    simpa only [sub_eq_add_neg, norm_neg] using
      IsUltrametricDist.norm_add_le_max y (-logRemainder (x : K))⟩
  let c : ℝ≥0 := ⟨cReal, hc0⟩
  have hlip : LipschitzWith c F := by
    apply LipschitzWith.of_dist_le_mul
    intro x z
    change dist (y - logRemainder (x : K)) (y - logRemainder (z : K)) ≤
      cReal * dist (x : K) (z : K)
    rw [dist_eq_norm, dist_eq_norm]
    have heq : (y - logRemainder (x : K)) - (y - logRemainder (z : K)) =
        -(logRemainder (x : K) - logRemainder (z : K)) := by ring
    rw [heq, norm_neg]
    exact norm_logRemainder_sub_le_sharp (p := p) _ _ r hr hc_lt.le
      x.property z.property
  have hcontract : ContractingWith c F := ⟨by change cReal < 1; exact hc_lt, hlip⟩
  let x := hcontract.fixedPoint F
  have hfixed : F x = x := hcontract.fixedPoint_isFixedPt
  have heq : y - logRemainder (x : K) = (x : K) := congrArg Subtype.val hfixed
  refine ⟨x, x.property, ?_⟩
  dsimp [logRemainder] at heq
  linear_combination -heq

end LocalField

section Consumer

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]

include localNormedAlgebra

/-- Every fractional norm lattice strictly inside the sharp inverse radius is
contained in the actual unscaled unit-log lattice.  This is the general
`a_i` interface consumed by the sharp log-shell lower bound. -/
theorem padicFractionalLattice_le_unitLogLattice_of_one_div_lt
    {a : ℝ} (ha : 1 / ((p : ℝ) - 1) < a) :
    padicFractionalLattice (p := p) (K := K) a ≤
      unitLogLattice (K := K) (p := p) := by
  intro y hy
  rw [mem_padicFractionalLattice_iff] at hy
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  have hnorm_lt : ‖y‖ < (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) := by
    exact hy.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hp1 (neg_lt_neg ha))
  obtain ⟨x, hx, hlog⟩ := exists_log1p_preimage_sharp (K := K) (p := p) (y := y)
    (norm_nonneg y) hnorm_lt le_rfl
  have hradius_le_one : (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) ≤ 1 := by
    have hp_sub_pos : 0 < (p : ℝ) - 1 := by
      linarith
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
      (neg_nonpos.mpr (one_div_nonneg.mpr hp_sub_pos.le))
  have hxlt : ‖x‖ < 1 := hx.trans_lt (hnorm_lt.trans_le hradius_le_one)
  let u := unitOfNormOne (K := K) ⟨1 + x, norm_one_add_of_norm_lt_one x hxlt⟩
  have hoffset : (u.val : K) - 1 = x := by
    change (1 + x) - 1 = x
    ring
  have hu : u ∈ principalUnits := by
    rw [mem_principalUnits_iff]
    rw [hoffset]
    exact hxlt
  change y ∈ (unitLogLattice (K := K) (p := p) : Set K)
  rw [coe_unitLogLattice_eq_range]
  refine ⟨u, ?_⟩
  rw [unitLog_eq_log1p (p := p) u hu, hoffset, hlog]

end Consumer

end

end LeanFormal.IUT.LocalFieldLogarithm

#print axioms LeanFormal.IUT.LocalFieldLogarithm.padicLog_denom_norm_inv_eq_rpow_padicValNat
#print axioms LeanFormal.IUT.LocalFieldLogarithm.padicValNat_cast_le_div_prime_sub_one
#print axioms LeanFormal.IUT.LocalFieldLogarithm.localLog_denom_norm_inv_eq_rpow_padicValNat
#print axioms LeanFormal.IUT.LocalFieldLogarithm.localLog_denom_norm_inv_le_sharp_rpow
#print axioms LeanFormal.IUT.LocalFieldLogarithm.norm_logRemainderTerm_sub_le_sharp
#print axioms LeanFormal.IUT.LocalFieldLogarithm.norm_logRemainder_sub_le_sharp
#print axioms LeanFormal.IUT.LocalFieldLogarithm.exists_log1p_preimage_sharp
#print axioms
  LeanFormal.IUT.LocalFieldLogarithm.padicFractionalLattice_le_unitLogLattice_of_one_div_lt
