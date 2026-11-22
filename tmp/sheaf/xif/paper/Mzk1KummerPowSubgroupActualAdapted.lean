/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Kummer: l-th power subgroups of a commutative monoid -/

namespace LeanFormal.IUT.XiFPaper.KummerPowSubgroupActual

variable (M : Type*) [CommMonoid M]

/-- The subgroup/monoid of l-th powers: the range of the l-th power map. -/
def powSubgroup (l : Nat) : Submonoid M := (powMonoidHom l).mrange

theorem mem_powSubgroup_iff {l : Nat} {x : M} :
    x ∈ powSubgroup M l ↔ ∃ y : M, y ^ l = x := by
  simp [powSubgroup]

theorem one_mem_powSubgroup (l : Nat) : (1 : M) ∈ powSubgroup M l := by
  rw [mem_powSubgroup_iff]
  exact ⟨1, one_pow l⟩

theorem powSubgroup_zero : powSubgroup M 0 = ⊤ := by
  ext x
  rw [mem_powSubgroup_iff]
  constructor
  · intro h
    exact Submonoid.mem_top x
  · intro h
    exact ⟨1, by simp⟩

end LeanFormal.IUT.XiFPaper.KummerPowSubgroupActual
