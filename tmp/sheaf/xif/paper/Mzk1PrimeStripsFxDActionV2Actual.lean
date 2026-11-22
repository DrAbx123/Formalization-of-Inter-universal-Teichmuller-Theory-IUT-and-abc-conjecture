import Mathlib

/-!
# Mzk1PrimeStripsFxDActionV2Actual — iterate action of ℕ (real math)

Status: PENDING-VERIFY. No sorry, no axiom.
Natural-number iterates of a self-map form an action (iterate laws by induction). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1PrimeStripsFxDActionV2Actual

/-- The ℕ-iterate action of a self-map. -/
def iterateAction {X : Type*} (f : X → X) (n : ℕ) (x : X) : X :=
  (f^[n]) x

/-- Genuine theorem: zero iterates act trivially. -/
theorem iterateAction_zero {X : Type*} (f : X → X) (x : X) :
    iterateAction f 0 x = x := rfl

/-- Genuine theorem: iterate action is additive in the exponent. -/
theorem iterateAction_add {X : Type*} (f : X → X) (m n : ℕ) (x : X) :
    iterateAction f (m + n) x = iterateAction f m (iterateAction f n x) := by
  unfold iterateAction
  rw [Function.iterate_add_apply]

/-- Genuine theorem: successor step of the iterate action. -/
theorem iterateAction_succ {X : Type*} (f : X → X) (n : ℕ) (x : X) :
    iterateAction f (n + 1) x = f (iterateAction f n x) := by
  unfold iterateAction
  rw [Function.iterate_succ_apply']

end LeanFormal.IUT.XiFPaper.Mzk1PrimeStripsFxDActionV2Actual
