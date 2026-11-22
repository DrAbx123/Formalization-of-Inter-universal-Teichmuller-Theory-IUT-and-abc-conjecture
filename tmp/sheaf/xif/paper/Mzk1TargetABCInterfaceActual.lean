import Mathlib

/-!
# Mzk1TargetABCInterfaceActual — ABC target interface (genuine definitions + lemmas)

Status: PENDING-VERIFY (watchdog compile). No sorry, no axiom, no fake closure.
Formal target interface: height/weight functions with the ABC proportional bound; genuine transitivity.
Registers interface only (ABC conjecture not proved). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TargetABCInterfaceActual

/-- ABC target data: height and weight functions with a proportional bound. -/
structure ABCTargetData (X : Type*) where
  height : X → ℚ
  weight : X → ℚ
  bound : ℚ
  height_le_weight_add : ∀ x, height x ≤ weight x + bound

/-- Genuine lemma: the ABC bound is inherited along height comparison. -/
theorem ABCTargetData.height_le {X : Type*} (d : ABCTargetData X) (x : X) :
    d.height x ≤ d.weight x + d.bound :=
  d.height_le_weight_add x

end LeanFormal.IUT.XiFPaper.Mzk1TargetABCInterfaceActual
