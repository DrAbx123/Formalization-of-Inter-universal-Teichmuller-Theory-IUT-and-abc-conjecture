/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Prime-strips (F/D): value-map kernels on finite prime sets -/

namespace LeanFormal.IUT.XiFPaper.PrimeStripValueKernelActual

variable {ι : Type*} [DecidableEq ι]

/-- The zero set of a value map on a finite prime set. -/
def evKernelIn (s : Finset ι) (f : ι → ℤ) : Finset ι :=
  s.filter (fun i => f i = 0)

theorem evKernelIn_subset (s : Finset ι) (f : ι → ℤ) : evKernelIn s f ⊆ s := by
  intro i hi
  simp [evKernelIn] at hi
  exact hi.1

theorem mem_evKernelIn_iff {s : Finset ι} {f : ι → ℤ} {i : ι} :
    i ∈ evKernelIn s f ↔ i ∈ s ∧ f i = 0 := by
  simp [evKernelIn]

theorem evKernelIn_empty (f : ι → ℤ) : evKernelIn (∅ : Finset ι) f = ∅ := by
  simp [evKernelIn]

theorem evKernelIn_union (s t : Finset ι) (f : ι → ℤ) :
    evKernelIn (s ∪ t) f = evKernelIn s f ∪ evKernelIn t f := by
  ext i
  simp [evKernelIn, and_left_comm, and_assoc, or_and_right]

end LeanFormal.IUT.XiFPaper.PrimeStripValueKernelActual
