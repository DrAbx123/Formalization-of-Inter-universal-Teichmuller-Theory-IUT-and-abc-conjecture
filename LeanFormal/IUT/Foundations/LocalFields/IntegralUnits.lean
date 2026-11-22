import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.GroupTheory.Coset.Card

/-!
# The actual integral unit group of a nonarchimedean local field

The source of the logarithm in IUT III Remark 1.2.2(i) is `O_kˣ`.
We use Mathlib's valuation-integer subring, identify its units with the
norm-one sphere of the field, and prove compactness from properness.
The source unit group and its topology are constructed, not supplied as
fields of an abstract log-shell record.
-/

namespace LeanFormal.IUT.LocalFieldIntegralUnits

noncomputable section

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- The actual valuation ring of the norm on the local field. -/
abbrev Integers (K : Type*) [NormedField K] [IsUltrametricDist K] :=
  (NormedField.valuation (K := K)).integer

theorem mem_integers_iff (x : K) : x ∈ Integers K ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem norm_unit_eq_one (u : (Integers K)ˣ) : ‖(u.val : K)‖ = 1 := by
  have hval : ‖(u.val : K)‖ ≤ 1 := (mem_integers_iff _).mp u.val.property
  have hinv : ‖((u⁻¹).val : K)‖ ≤ 1 := (mem_integers_iff _).mp (u⁻¹).val.property
  have hmul : (u.val : K) * ((u⁻¹).val : K) = 1 := by
    exact_mod_cast u.val_inv
  apply le_antisymm hval
  calc
    1 = ‖(u.val : K)‖ * ‖((u⁻¹).val : K)‖ := by rw [← norm_mul, hmul, norm_one]
    _ ≤ ‖(u.val : K)‖ := mul_le_of_le_one_right (norm_nonneg _) hinv

omit [IsUltrametricDist K] in
theorem norm_one_ne_zero (x : {x : K | ‖x‖ = 1}) : (x : K) ≠ 0 := by
  intro hx
  have hnorm : ‖(x : K)‖ = 1 := x.property
  rw [hx, norm_zero] at hnorm
  exact zero_ne_one hnorm

/-- A norm-one field element is an integral unit, with its actual field inverse. -/
def unitOfNormOne (x : {x : K | ‖x‖ = 1}) : (Integers K)ˣ where
  val := ⟨x, (mem_integers_iff _).mpr x.property.le⟩
  inv := ⟨(x : K)⁻¹, (mem_integers_iff _).mpr (by rw [norm_inv, x.property]; simp)⟩
  val_inv := Subtype.ext (mul_inv_cancel₀ (norm_one_ne_zero x))
  inv_val := Subtype.ext (inv_mul_cancel₀ (norm_one_ne_zero x))

/-- The topology on the actual unit group agrees with the field's norm-one
sphere, including the inverse coordinate in the topology of units. -/
def unitsNormOneHomeomorph : (Integers K)ˣ ≃ₜ {x : K | ‖x‖ = 1} where
  toFun u := ⟨u.val, norm_unit_eq_one u⟩
  invFun := unitOfNormOne
  left_inv u := by apply Units.ext; rfl
  right_inv x := by rfl
  continuous_toFun := (continuous_subtype_val.comp Units.continuous_val).subtype_mk _
  continuous_invFun := by
    apply Units.continuous_iff.mpr
    constructor
    · exact continuous_subtype_val.subtype_mk _
    · exact (continuous_subtype_val.inv₀ norm_one_ne_zero).subtype_mk _

/-- Compactness of the actual full integral unit group, not only of a
principal-unit calibration subgroup. -/
theorem compactSpace_units [ProperSpace K] : CompactSpace (Integers K)ˣ := by
  have heq : {x : K | ‖x‖ = 1} = Metric.sphere (0 : K) 1 := by
    ext x
    simp
  have hc : IsCompact {x : K | ‖x‖ = 1} := heq ▸ isCompact_sphere (0 : K) 1
  letI := isCompact_iff_compactSpace.mp hc
  have h := isCompact_univ.image (unitsNormOneHomeomorph (K := K)).symm.continuous
  rw [Set.image_univ, (unitsNormOneHomeomorph (K := K)).symm.surjective.range_eq] at h
  exact ⟨h⟩

/-- The actual principal-unit subgroup `1 + m_k` inside the full integral
unit group. This is not restricted to base-field principal units. -/
def principalUnits : Subgroup (Integers K)ˣ where
  carrier := {u | ‖(u.val : K) - 1‖ < 1}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    change ‖(u.val : K) - 1‖ < 1 at hu
    change ‖(v.val : K) - 1‖ < 1 at hv
    have heq : ((u * v).val : K) - 1 =
        (u.val : K) * ((v.val : K) - 1) + ((u.val : K) - 1) := by
      simp only [Units.val_mul, Subring.coe_mul]
      ring
    change ‖((u * v).val : K) - 1‖ < 1
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
    change ‖((u⁻¹).val : K) - 1‖ < 1
    rw [heq, norm_mul, norm_neg, norm_unit_eq_one, one_mul]
    exact hu

theorem mem_principalUnits_iff (u : (Integers K)ˣ) :
    u ∈ principalUnits ↔ ‖(u.val : K) - 1‖ < 1 := Iff.rfl

/-- The principal units are open in the actual compact unit group. -/
theorem isOpen_principalUnits : IsOpen (principalUnits (K := K) : Set (Integers K)ˣ) :=
  isOpen_lt (continuous_norm.comp
    ((continuous_subtype_val.comp Units.continuous_val).sub continuous_const)) continuous_const

/-- The quotient by principal units is finite, proved directly from the
actual compact group and its open principal-unit subgroup. -/
theorem finite_principalUnitQuotient [ProperSpace K] :
    Finite ((Integers K)ˣ ⧸ principalUnits (K := K)) := by
  letI := compactSpace_units (K := K)
  letI := QuotientGroup.discreteTopology (N := principalUnits (K := K)) isOpen_principalUnits
  exact finite_of_compact_of_discrete

/-- A single nonzero exponent sends every integral unit into principal units.
It is constructed from the finite quotient, not added as source data. -/
theorem exists_uniform_principalUnit_exponent [ProperSpace K] :
    ∃ N : ℕ, 0 < N ∧ ∀ u : (Integers K)ˣ, u ^ N ∈ principalUnits := by
  letI := finite_principalUnitQuotient (K := K)
  letI := Fintype.ofFinite ((Integers K)ˣ ⧸ principalUnits (K := K))
  refine ⟨Fintype.card ((Integers K)ˣ ⧸ principalUnits (K := K)), Fintype.card_pos, ?_⟩
  intro u
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
  exact pow_card_eq_one

end

end LeanFormal.IUT.LocalFieldIntegralUnits
