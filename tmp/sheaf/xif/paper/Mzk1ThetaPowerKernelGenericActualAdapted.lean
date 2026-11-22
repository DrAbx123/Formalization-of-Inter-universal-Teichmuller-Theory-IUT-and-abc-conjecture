/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Theta power kernels: generic l-th power torsion subgroups -/

namespace LeanFormal.IUT.XiFPaper.ThetaPowerKernelGenericActual

variable (G : Type*) [Group G]

/-- The subgroup of l-th power torsion elements: x^l = 1. -/
def powTorsion (l : Nat) : Subgroup G := (powMonoidHom l).ker

theorem mem_powTorsion_iff {l : Nat} {x : G} : x ∈ powTorsion G l ↔ x ^ l = 1 :=
  MonoidHom.mem_ker

theorem powTorsion_one : powTorsion G 1 = ⊥ := by
  ext x
  rw [mem_powTorsion_iff, Subgroup.mem_bot]
  simp

theorem powTorsion_le_of_dvd {l m : Nat} (h : l ∣ m) : powTorsion G m ≤ powTorsion G l := by
  intro x hx
  rw [mem_powTorsion_iff] at hx ⊢
  obtain ⟨k, rfl⟩ := h
  rw [pow_mul, hx, one_pow]

theorem powTorsion_le (l : Nat) : powTorsion G l ≤ (⊤ : Subgroup G) := le_top

end LeanFormal.IUT.XiFPaper.ThetaPowerKernelGenericActual
