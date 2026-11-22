/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Prime-strips: degree sums of exponent vectors -/

namespace LeanFormal.IUT.XiFPaper.PrimeStripDegreeActual

open BigOperators

variable {ι : Type*}

/-- The degree of an exponent vector on a finite prime set. -/
def stripDegree (s : Finset ι) (v : ι → ℤ) : ℤ := ∑ i in s, v i

@[simp] theorem stripDegree_zero (s : Finset ι) :
    stripDegree s (fun _ => 0) = 0 := by
  simp [stripDegree]

theorem stripDegree_add (s : Finset ι) (a b : ι → ℤ) :
    stripDegree s (fun i => a i + b i) = stripDegree s a + stripDegree s b := by
  simp [stripDegree, Finset.sum_add_distrib]

theorem stripDegree_mono (s : Finset ι) {a b : ι → ℤ}
    (h : ∀ i ∈ s, a i ≤ b i) : stripDegree s a ≤ stripDegree s b := by
  exact Finset.sum_le_sum h

theorem stripDegree_neg (s : Finset ι) (a : ι → ℤ) :
    stripDegree s (fun i => -a i) = -stripDegree s a := by
  simp [stripDegree]

theorem stripDegree_sub (s : Finset ι) (a b : ι → ℤ) :
    stripDegree s (fun i => a i - b i) = stripDegree s a - stripDegree s b := by
  simp [stripDegree, Finset.sum_sub_distrib]

end LeanFormal.IUT.XiFPaper.PrimeStripDegreeActual
