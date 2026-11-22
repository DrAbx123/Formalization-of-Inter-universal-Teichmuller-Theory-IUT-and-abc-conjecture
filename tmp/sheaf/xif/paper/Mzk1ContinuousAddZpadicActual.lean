import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ContinuousAddZpadicActual

open scoped BigOperators
open PadicInt

/-- Every additive homomorphism between finite powers of `ℤ_[p]` is
continuous for the standard topology.  The proof uses the `p^n`-neighbourhood
basis: an additive map sends integer multiples `p^n • x` to `p^n • f x`, hence
maps a sufficiently small lattice neighbourhood into a prescribed one. -/
theorem continuous_of_addHom_fin_zpadic {p : Nat} [Fact p.Prime]
    {d d' : Nat}
    (f : (Fin d → ℤ_[p]) →+ (Fin d' → ℤ_[p])) : Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hp_ne : (p : ℤ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hp_pos : 0 < ‖(p : ℤ_[p])‖ := norm_pos_iff.mpr hp_ne
  have hp_lt_one : ‖(p : ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hp_lt_one
  refine ⟨‖(p : ℤ_[p])‖ ^ n, pow_pos hp_pos n, ?_⟩
  intro x hx
  have hx' : ‖x‖ < ‖(p : ℤ_[p])‖ ^ n := by
    simpa [dist_eq_norm] using hx
  have hrpow : ‖(p : ℤ_[p])‖ ^ n = (p : ℝ) ^ (-(n : ℤ)) := by
    rw [← norm_pow]
    exact PadicInt.norm_p_pow n
  have hxi_mem : ∀ i, x i ∈ (Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) := by
    intro i
    apply (PadicInt.norm_le_pow_iff_mem_span_pow (x i) n).mp
    have hxi : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
    exact (le_of_lt (lt_of_le_of_lt hxi hx')).trans (le_of_eq hrpow)
  let c : Fin d → ℤ_[p] := fun i =>
    Classical.choose (Ideal.mem_span_singleton.mp (hxi_mem i))
  have hc : ∀ i, x i = (p : ℤ_[p]) ^ n * c i := by
    intro i
    exact Classical.choose_spec (Ideal.mem_span_singleton.mp (hxi_mem i))
  have hxeq : x = (p ^ n : Nat) • c := by
    funext i
    rw [hc i]
    change (p : ℤ_[p]) ^ n * c i = (p ^ n : Nat) • (c i)
    rw [nsmul_eq_mul, Nat.cast_pow]
  have hfx : f x = (p ^ n : Nat) • f c := by
    rw [hxeq, map_nsmul]
  rw [hfx]
  have hdist : dist ((p ^ n : Nat) • f c) (f 0) < ε ↔
      ‖(p ^ n : Nat) • f c‖ < ε := by
    simp [dist_eq_norm]
  rw [hdist]
  rw [pi_norm_lt_iff (r := ε) hε]
  intro j
  have hcoord : ((p ^ n : Nat) • f c) j = (p ^ n : Nat) • (f c j) := rfl
  rw [hcoord]
  calc
    ‖(p ^ n : Nat) • (f c j)‖
        = ‖(p : ℤ_[p]) ^ n * (f c j)‖ := by
          rw [nsmul_eq_mul, Nat.cast_pow]
    _ = ‖(p : ℤ_[p])‖ ^ n * ‖f c j‖ := by rw [norm_mul, norm_pow]
    _ ≤ ‖(p : ℤ_[p])‖ ^ n * 1 := by
          exact mul_le_mul_of_nonneg_left (PadicInt.norm_le_one (f c j))
            (pow_nonneg hp_pos.le n)
    _ = ‖(p : ℤ_[p])‖ ^ n := mul_one _
    _ < ε := hn

#print axioms continuous_of_addHom_fin_zpadic
end LeanFormal.IUT.XiFPaper.Mzk1ContinuousAddZpadicActual