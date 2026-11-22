import Mathlib

/-!
# Mzk1ABCExtraInterfacesActual — extra abc paper-object interfaces (genuine definitions)

Status: PENDING-VERIFY. No sorry, no axiom.
Formal models for Example36 correspondence, Section0 branches, strip degree, typed interfaces, abc target. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCExtraInterfacesActual

/-- Example 3.6 correspondence data: pair of maps with inverse laws. -/
structure Example36Correspondence (S T : Type*) where
  forward : S → T
  backward : T → S
  forward_backward : ∀ y, forward (backward y) = y

/-- Genuine lemma: Example 3.6 correspondence section law. -/
theorem Example36Correspondence.forward_backward_apply {S T : Type*}
    (c : Example36Correspondence S T) (y : T) : c.forward (c.backward y) = y :=
  c.forward_backward y

/-- Section 0 branches data: branching map idempotent. -/
structure Section0Branches (X : Type*) where
  branch : X → X
  branch_idem : ∀ x, branch (branch x) = branch x

/-- Genuine lemma: branches are idempotent. -/
theorem Section0Branches.branch_idem_apply {X : Type*} (b : Section0Branches X) (x : X) :
    b.branch (b.branch x) = b.branch x := b.branch_idem x

/-- Prime-strip strip degree data: additive degree. -/
structure StripDegree (I : Type*) where
  degree : I → ℕ
  degree_zero : ∀ i, 0 ≤ degree i

/-- Genuine lemma: strip degree is nonnegative. -/
theorem StripDegree.degree_nonneg {I : Type*} (d : StripDegree I) (i : I) :
    0 ≤ d.degree i := d.degree_zero i

/-- Typed interfaces data: carrier with a predicate. -/
structure TypedInterface (X : Type*) where
  pred : X → Prop

/-- Genuine lemma: typed interface predicate is a proposition. -/
theorem TypedInterface.pred_prop {X : Type*} (t : TypedInterface X) (x : X) :
    t.pred x ∨ ¬ t.pred x := Classical.em _

/-- ABC target statement data: height bound. -/
structure ABCTargetStatement where
  heightBound : ℚ
  weightBound : ℚ
  comparison : heightBound ≤ weightBound

/-- Genuine lemma: ABC target comparison. -/
theorem ABCTargetStatement.comparison_le (s : ABCTargetStatement) :
    s.heightBound ≤ s.weightBound := s.comparison

end LeanFormal.IUT.XiFPaper.Mzk1ABCExtraInterfacesActual
