import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits

/-!
# Arbitrarily small congruence subgroups of the actual integral unit group

Every positive-radius neighborhood of one of the form `‖u-1‖ < r` is an
open subgroup of the actual integral units. Properness makes the full
unit group compact, so the quotient is finite and a single positive
exponent sends every unit into that neighborhood. This supplies the
small-unit step in identifying the kernel of the analytic logarithm.
-/

namespace LeanFormal.IUT.LocalFieldIntegralUnits

noncomputable section

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

def principalUnitsAtRadius (r : ℝ) (hr : 0 < r) : Subgroup (Integers K)ˣ where
  carrier := {u | ‖(u.val : K) - 1‖ < r}
  one_mem' := by simpa using hr
  mul_mem' := by
    intro u v hu hv
    change ‖(u.val : K) - 1‖ < r at hu
    change ‖(v.val : K) - 1‖ < r at hv
    have heq : ((u * v).val : K) - 1 =
        (u.val : K) * ((v.val : K) - 1) + ((u.val : K) - 1) := by
      simp only [Units.val_mul, Subring.coe_mul]
      ring
    change ‖((u * v).val : K) - 1‖ < r
    rw [heq]
    apply lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
    apply max_lt
    · simpa only [norm_mul, norm_unit_eq_one, one_mul] using hv
    · exact hu
  inv_mem' := by
    intro u hu
    have hmul : ((u⁻¹).val : K) * (u.val : K) = 1 := by exact_mod_cast u.inv_val
    have heq : ((u⁻¹).val : K) - 1 =
        -((u⁻¹).val : K) * ((u.val : K) - 1) := by
      linear_combination hmul
    change ‖((u⁻¹).val : K) - 1‖ < r
    rw [heq, norm_mul, norm_neg, norm_unit_eq_one, one_mul]
    exact hu

theorem mem_principalUnitsAtRadius_iff (r : ℝ) (hr : 0 < r) (u : (Integers K)ˣ) :
    u ∈ principalUnitsAtRadius r hr ↔ ‖(u.val : K) - 1‖ < r := Iff.rfl

theorem isOpen_principalUnitsAtRadius (r : ℝ) (hr : 0 < r) :
    IsOpen (principalUnitsAtRadius (K := K) r hr : Set (Integers K)ˣ) :=
  isOpen_lt (continuous_norm.comp
    ((continuous_subtype_val.comp Units.continuous_val).sub continuous_const)) continuous_const

theorem finite_principalUnitsAtRadius_quotient [ProperSpace K] (r : ℝ) (hr : 0 < r) :
    Finite ((Integers K)ˣ ⧸ principalUnitsAtRadius (K := K) r hr) := by
  letI := compactSpace_units (K := K)
  letI := QuotientGroup.discreteTopology (N := principalUnitsAtRadius (K := K) r hr)
    (isOpen_principalUnitsAtRadius r hr)
  exact finite_of_compact_of_discrete

/-- The exponent is produced by a finite quotient, at any specified small
radius, not by an assumed convergence property of powers of units. -/
theorem exists_uniform_smallUnit_exponent [ProperSpace K] (r : ℝ) (hr : 0 < r) :
    ∃ n : ℕ, 0 < n ∧ ∀ u : (Integers K)ˣ, ‖((u ^ n).val : K) - 1‖ < r := by
  letI := finite_principalUnitsAtRadius_quotient (K := K) r hr
  letI := Fintype.ofFinite ((Integers K)ˣ ⧸ principalUnitsAtRadius (K := K) r hr)
  refine ⟨Fintype.card ((Integers K)ˣ ⧸ principalUnitsAtRadius (K := K) r hr),
    Fintype.card_pos, ?_⟩
  intro u
  apply (mem_principalUnitsAtRadius_iff r hr _).mp
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
  exact pow_card_eq_one

end

end LeanFormal.IUT.LocalFieldIntegralUnits
