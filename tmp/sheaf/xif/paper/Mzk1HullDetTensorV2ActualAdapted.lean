import Mathlib

/-!
# Mzk1HullDetTensorV2ActualAdapted (adapted copy, A475 reuse) — Hull determinant tensor interface (V2; fixed instance binders)

Status: PENDING-VERIFY (watchdog). No sorry, no axiom.
V2 route-around of red Mzk1HullDetTensorActual (missing [Mul M] [One M] instance binders).
Genuine determinant data interface with instance parameters. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullDetTensorV2ActualAdapted

/-- Determinant data: multiplicative Q-valued function on a monoid. -/
structure DetData (M : Type*) [Mul M] [One M] where
  det : M → ℚ
  det_mul : ∀ x y, det (x * y) = det x * det y
  det_one : det 1 = 1

/-- Genuine lemma: determinant of a product. -/
theorem DetData.det_mul_apply {M : Type*} [Mul M] [One M] (d : DetData M) (x y : M) :
    d.det (x * y) = d.det x * d.det y :=
  d.det_mul x y

end LeanFormal.IUT.XiFPaper.Mzk1HullDetTensorV2ActualAdapted
