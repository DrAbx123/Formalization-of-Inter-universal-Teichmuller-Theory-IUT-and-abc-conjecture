/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PrimeStripDegreeActual

/-! # Prime-strips: chain — nonneg degree and comparison corollaries -/

namespace LeanFormal.IUT.XiFPaper.PrimeStripDegreeActual

variable {ι : Type*}

theorem stripDegree_nonneg (s : Finset ι) {v : ι → ℤ}
    (h : ∀ i ∈ s, 0 ≤ v i) : 0 ≤ stripDegree s v := by
  unfold stripDegree
  exact Finset.sum_nonneg h

theorem stripDegree_le_of_pointwise (s : Finset ι) {a b : ι → ℤ}
    (h : ∀ i ∈ s, a i ≤ b i) : stripDegree s a ≤ stripDegree s b := 
  stripDegree_mono s h

theorem stripDegree_zero_iff (s : Finset ι) {v : ι → ℤ}
    (hv : ∀ i ∈ s, 0 ≤ v i) : stripDegree s v = 0 ↔ ∀ i ∈ s, v i = 0 := by
  unfold stripDegree
  rw [Finset.sum_eq_zero_iff_of_nonneg hv]
  constructor
  · intro h i hi
    exact h i hi
  · intro h i hi
    exact h i hi

end LeanFormal.IUT.XiFPaper.PrimeStripDegreeActual
