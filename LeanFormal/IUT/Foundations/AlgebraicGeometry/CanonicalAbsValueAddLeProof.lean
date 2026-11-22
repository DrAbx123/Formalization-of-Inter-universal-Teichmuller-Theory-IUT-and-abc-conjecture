import LeanFormal.IUT.Foundations.AlgebraicGeometry.GeneralNormalizedNormBySpectralUniqueness
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

/-!
# Nonarchimedean triangle inequality for the canonical absolute value

Downstream consumer of `GeneralNormalizedNormBySpectralUniqueness`.  It records
that the canonical absolute value `f x = absNorm ^ (-(ν x)/d)` (with `f 0 = 0`)
satisfies the stronger nonarchimedean bound

  `f (x + y) ≤ max (f x) (f y)`,

from which the archimedean `AbsoluteValue.add_le'` field is derived in the
donor.  This file is not imported by the donor (no cycle).
-/

noncomputable section

namespace LeanFormal.IUT.CanonicalAbsValueAddLeProof

open scoped WithZero Valued Topology
open LeanFormal.IUT
open LeanFormal.IUT.GeneralNormalizedNormBySpectralUniqueness
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {F : Type u} [Field F] [NumberField F] (place : NumberField.FinitePlace F)

abbrev L : Type u := LeanFormal.IUT.NumberFieldFinitePlace.NormalizedCompletion place

/-- The canonical absolute value satisfies the nonarchimedean triangle
inequality. -/
theorem canonicalAbsValue_add_le (x y : L place) :
    canonicalAbsValue place (x + y) ≤
      max (canonicalAbsValue place x) (canonicalAbsValue place y) := by
  show canonicalFun place (x + y) ≤ max (canonicalFun place x) (canonicalFun place y)
  by_cases hx : x = 0
  · subst hx
    rw [zero_add, canonicalFun_zero]
    exact le_max_right _ _
  · by_cases hy : y = 0
    · subst hy
      rw [add_zero, canonicalFun_zero]
      exact le_max_left _ _
    · by_cases hxy : x + y = 0
      · rw [hxy, canonicalFun_zero]
        exact le_trans (canonicalFun_nonneg place x) (le_max_left _ _)
      · exact canonicalFun_add_le place x y hx hy hxy

end LeanFormal.IUT.CanonicalAbsValueAddLeProof

end