import Mathlib

/-!
# Mzk1KummerPowerSubgroupV2Actual — power subgroups of abelian groups (real math)

Status: PENDING-VERIFY. No sorry, no axiom.
Subgroup of n-th powers in a commutative group; closure proofs are genuine. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1KummerPowerSubgroupV2Actual

/-- The set of n-th powers in a commutative group. -/
def powSubgroupSet (G : Type*) [CommGroup G] (n : ℕ) : Set G := { g | ∃ x, x ^ n = g }

/-- Genuine theorem: the identity is an n-th power (n>0). -/
theorem one_mem_powSubgroupSet (G : Type*) [CommGroup G] {n : ℕ} (hn : 0 < n) :
    (1 : G) ∈ powSubgroupSet G n := by
  refine ⟨1, ?_⟩
  exact one_pow n

/-- Genuine theorem: product of n-th powers is an n-th power. -/
theorem mul_mem_powSubgroupSet (G : Type*) [CommGroup G] {n : ℕ}
    {a b : G} (ha : a ∈ powSubgroupSet G n) (hb : b ∈ powSubgroupSet G n) :
    a * b ∈ powSubgroupSet G n := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  refine ⟨x * y, ?_⟩
  rw [mul_pow]

/-- Genuine theorem: inverse of an n-th power is an n-th power. -/
theorem inv_mem_powSubgroupSet (G : Type*) [CommGroup G] {n : ℕ}
    {a : G} (ha : a ∈ powSubgroupSet G n) : a⁻¹ ∈ powSubgroupSet G n := by
  obtain ⟨x, rfl⟩ := ha
  refine ⟨x⁻¹, ?_⟩
  rw [inv_pow]

/-- The n-th power subgroup as a subgroup (closure bundled). -/
def powSubgroup (G : Type*) [CommGroup G] (n : ℕ) (hn : 0 < n) : Subgroup G where
  carrier := powSubgroupSet G n
  one_mem' := one_mem_powSubgroupSet G hn
  mul_mem' := fun ha hb => mul_mem_powSubgroupSet G ha hb
  inv_mem' := fun ha => inv_mem_powSubgroupSet G ha

end LeanFormal.IUT.XiFPaper.Mzk1KummerPowerSubgroupV2Actual
