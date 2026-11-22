import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits

/-!
# Closed-radius congruence subgroups of actual integral units

The scaled logarithm uses the closed ball of radius norm(p*), so the strict
congruence subgroups alone do not identify its image with the full integer
ring. Ultrametricity makes these positive closed-radius subgroups open, and
compactness of the actual unit group makes their quotients finite.
-/

namespace LeanFormal.IUT.LocalFieldIntegralUnits

open scoped Topology

noncomputable section

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

def principalUnitsAtClosedRadius (r : ℝ) (hr : 0 ≤ r) : Subgroup (Integers K)ˣ where
  carrier := {u | ‖(u.val : K) - 1‖ ≤ r}
  one_mem' := by simpa using hr
  mul_mem' := by
    intro u v hu hv
    change ‖(u.val : K) - 1‖ ≤ r at hu
    change ‖(v.val : K) - 1‖ ≤ r at hv
    have heq : ((u * v).val : K) - 1 =
        (u.val : K) * ((v.val : K) - 1) + ((u.val : K) - 1) := by
      simp only [Units.val_mul, Subring.coe_mul]
      ring
    change ‖((u * v).val : K) - 1‖ ≤ r
    rw [heq]
    apply (IsUltrametricDist.norm_add_le_max _ _).trans
    apply max_le
    · simpa only [norm_mul, norm_unit_eq_one, one_mul] using hv
    · exact hu
  inv_mem' := by
    intro u hu
    have hmul : ((u⁻¹).val : K) * (u.val : K) = 1 := by exact_mod_cast u.inv_val
    have heq : ((u⁻¹).val : K) - 1 =
        -((u⁻¹).val : K) * ((u.val : K) - 1) := by linear_combination hmul
    change ‖((u⁻¹).val : K) - 1‖ ≤ r
    rw [heq, norm_mul, norm_neg, norm_unit_eq_one, one_mul]
    exact hu

theorem mem_principalUnitsAtClosedRadius_iff (r : ℝ) (hr : 0 ≤ r) (u : (Integers K)ˣ) :
    u ∈ principalUnitsAtClosedRadius r hr ↔ ‖(u.val : K) - 1‖ ≤ r := Iff.rfl

theorem isOpen_principalUnitsAtClosedRadius (r : ℝ) (hr : 0 < r) :
    IsOpen (principalUnitsAtClosedRadius (K := K) r hr.le : Set (Integers K)ˣ) := by
  apply isOpen_iff_mem_nhds.mpr
  intro u hu
  change ‖(u.val : K) - 1‖ ≤ r at hu
  have hnear : IsOpen {v : (Integers K)ˣ | ‖(v.val : K) - (u.val : K)‖ < r} :=
    isOpen_lt (continuous_norm.comp
      ((continuous_subtype_val.comp Units.continuous_val).sub continuous_const)) continuous_const
  have hself : u ∈ {v : (Integers K)ˣ | ‖(v.val : K) - (u.val : K)‖ < r} := by
    simpa using hr
  apply Filter.mem_of_superset (hnear.mem_nhds hself)
  intro v hv
  change ‖(v.val : K) - 1‖ ≤ r
  have heq : (v.val : K) - 1 =
      ((v.val : K) - (u.val : K)) + ((u.val : K) - 1) := by ring
  rw [heq]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hv.le hu)

theorem finite_principalUnitsAtClosedRadius_quotient [ProperSpace K] (r : ℝ) (hr : 0 < r) :
    Finite ((Integers K)ˣ ⧸ principalUnitsAtClosedRadius (K := K) r hr.le) := by
  letI := compactSpace_units (K := K)
  letI := QuotientGroup.discreteTopology (N := principalUnitsAtClosedRadius (K := K) r hr.le)
    (isOpen_principalUnitsAtClosedRadius r hr)
  exact finite_of_compact_of_discrete

end

end LeanFormal.IUT.LocalFieldIntegralUnits
