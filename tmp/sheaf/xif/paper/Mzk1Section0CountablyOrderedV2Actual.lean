import Mathlib

/-!
# Mzk1Section0CountablyOrderedV2Actual — countably ordered ℤ-valued sequences (real math)

Status: PENDING-VERIFY. No sorry, no axiom.
Strict step implies strict monotonicity and order preservation (real induction/monotonicity proof). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0CountablyOrderedV2Actual

/-- A sequence with strict successor steps. -/
def StrictStepSeq (f : ℕ → ℤ) : Prop := ∀ n, f n < f (n + 1)

/-- Genuine theorem: strict steps imply strict monotonicity. -/
theorem strictStep_strictMono {f : ℕ → ℤ} (h : StrictStepSeq f) :
    StrictMono f :=
  strictMono_nat_of_lt_succ h

/-- Genuine theorem: strict steps imply monotonicity. -/
theorem strictStep_monotone {f : ℕ → ℤ} (h : StrictStepSeq f) : Monotone f :=
  (strictStep_strictMono h).monotone

/-- Genuine theorem: order preservation along ℕ. -/
theorem strictStep_le {f : ℕ → ℤ} (h : StrictStepSeq f) :
    ∀ {n m : ℕ}, n ≤ m → f n ≤ f m :=
  fun hnm => (strictStep_monotone h) hnm

end LeanFormal.IUT.XiFPaper.Mzk1Section0CountablyOrderedV2Actual
