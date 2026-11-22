import Mathlib
example {K : Type*} [Field K] [Algebra ℚ K] (q : ℚ) : algebraMap ℚ K q = (q : K) := by
  rw [← map_ratCast (algebraMap ℚ K) q]
  rfl
