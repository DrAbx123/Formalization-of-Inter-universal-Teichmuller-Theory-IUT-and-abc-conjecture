import Mathlib

/-! # Source contraction radius for t = j^{-1}

Exact source local-field assumptions (matching the production Frey/Tate input
theorems in LeanFormal/IUT/ABCBridge/Geometry/ABCModelHeightComparison.lean):
L is a complete nonarchimedean normed field with ultrametric norm; the source
element is t = j^{-1} (the Frey candidate q = freyAbcTateCandidateQ p a b c,
viewed in Q_[p]), with t != 0 and ||t|| < 1.  From ||t|| < 1 we construct
c = (1 + ||t||)/2 with ||t|| <= c < 1 and prove the norm facts used by the
c-contraction.  Scratch only; no production edits. -/

noncomputable section

namespace LeanFormal.IUT.SourceContraction

variable {L : Type*} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- The explicit contraction radius c = (1 + ||t||)/2. -/
noncomputable def sourceContractionRadius (t : L) : ℝ :=
  (1 + ‖t‖) / 2

/-- The source radius is nonnegative. -/
theorem sourceContractionRadius_nonneg (t : L) :
    0 ≤ sourceContractionRadius t := by
  unfold sourceContractionRadius
  positivity

/-- The source element is bounded by the radius: ||t|| <= c. -/
theorem norm_le_sourceContractionRadius {t : L} (ht : ‖t‖ < 1) :
    ‖t‖ ≤ sourceContractionRadius t := by
  unfold sourceContractionRadius
  linarith [norm_nonneg t]

/-- The radius is strictly below one: c < 1. -/
theorem sourceContractionRadius_lt_one {t : L} (ht : ‖t‖ < 1) :
    sourceContractionRadius t < 1 := by
  unfold sourceContractionRadius
  linarith

/-- The radius is at most one. -/
theorem sourceContractionRadius_le_one {t : L} (ht : ‖t‖ < 1) :
    sourceContractionRadius t ≤ 1 :=
  (sourceContractionRadius_lt_one ht).le

/-- The contraction gap is positive: 0 < 1 - c. -/
theorem one_sub_sourceContractionRadius_pos {t : L} (ht : ‖t‖ < 1) :
    0 < 1 - sourceContractionRadius t := by
  linarith [sourceContractionRadius_lt_one ht]

/-- Power norm bound: ||t^n|| <= c^n for every n. -/
theorem norm_pow_le_sourceContractionRadius_pow {t : L} (ht : ‖t‖ < 1) (n : Nat) :
    ‖t ^ n‖ ≤ sourceContractionRadius t ^ n := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg t) (norm_le_sourceContractionRadius ht) n

/-- The geometric majorant of the c-contraction is summable. -/
theorem summable_sourceContractionRadius_pow {t : L} (ht : ‖t‖ < 1) :
    Summable (fun n : Nat => sourceContractionRadius t ^ n) :=
  summable_geometric_of_lt_one (sourceContractionRadius_nonneg t)
    (sourceContractionRadius_lt_one ht)

/-- The source powers are summable by comparison with the geometric majorant. -/
theorem summable_source_pow_of_norm_lt_one {t : L} (ht : ‖t‖ < 1) :
    Summable (fun n : Nat => t ^ n) := by
  have hmajor : Summable (fun n : Nat => sourceContractionRadius t ^ n) :=
    summable_sourceContractionRadius_pow ht
  have hnorm : Summable (fun n : Nat => ‖t ^ n‖) :=
    hmajor.of_nonneg_of_le (fun n => norm_nonneg _) (fun n =>
      norm_pow_le_sourceContractionRadius_pow ht n)
  exact hnorm.of_norm

/-- The source contraction gap controls the tail: c^n <= c^n (trivial form
recorded for the c-contraction interface). -/
theorem sourceContractionRadius_pow_nonneg (t : L) (n : Nat) :
    0 ≤ sourceContractionRadius t ^ n :=
  pow_nonneg (sourceContractionRadius_nonneg t) n

end LeanFormal.IUT.SourceContraction
