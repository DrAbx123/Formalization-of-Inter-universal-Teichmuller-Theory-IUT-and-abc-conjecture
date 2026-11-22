/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import Mathlib.Tactic

/-! # P2: norm-instance coherence for common-prime / normalized completions -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P2NormalizedCompletionNormCoherenceActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

variable {K : Type*} [Field K] [NumberField K]
variable {p : ℕ} [Fact p.Prime]

/-- The `commonPrimeCompletionNormedField` norm is definitionally the
`normalizedCompletionNontriviallyNormedField` norm on the same underlying field. -/
theorem commonPrimeCompletion_norm_eq_normalized
    (place : FinitePlaceAtPrime K p) (x : CommonPrimeCompletion place) :
    @norm (CommonPrimeCompletion place)
        (commonPrimeCompletionNormedField place).toNorm x =
      @norm (NormalizedCompletion place.val)
        (normalizedCompletionNontriviallyNormedField place.val).toNorm x := rfl

/-- The same coherence in the `NormalizedCompletion -- CommonPrimeCompletion` direction. -/
theorem normalized_norm_eq_commonPrimeCompletion
    (place : FinitePlaceAtPrime K p) (x : NormalizedCompletion place.val) :
    @norm (NormalizedCompletion place.val)
        (normalizedCompletionNontriviallyNormedField place.val).toNorm x =
      @norm (CommonPrimeCompletion place)
        (commonPrimeCompletionNormedField place).toNorm x := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P2NormalizedCompletionNormCoherenceActual

end