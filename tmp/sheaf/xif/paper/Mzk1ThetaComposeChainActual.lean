import Mathlib

/-!
# Mzk1ThetaComposeChainActual — chained Theta-link composition (genuine)

Status: PENDING-VERIFY. No sorry, no axiom.
Chained consumer: composing two bi-invertible theta-links yields a bi-invertible theta-link. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaComposeChainActual

/-- Bi-invertible theta-link data between two carriers. -/
structure ThetaLinkBi (S T : Type*) where
  toT : S → T
  toS : T → S
  left_inv : ∀ x, toS (toT x) = x
  right_inv : ∀ y, toT (toS y) = y

/-- Chained: composition of two bi-invertible theta-links. -/
def ThetaLinkBi.compose {S T U : Type*} (e1 : ThetaLinkBi S T) (e2 : ThetaLinkBi T U) :
    ThetaLinkBi S U where
  toT := fun x => e2.toT (e1.toT x)
  toS := fun y => e1.toS (e2.toS y)
  left_inv := by
    intro x
    rw [e2.left_inv]
    exact e1.left_inv x
  right_inv := by
    intro y
    rw [e1.right_inv]
    exact e2.right_inv y

/-- Chained: the composed theta-link is bi-invertible (left inverse law applies). -/
theorem ThetaLinkBi.compose_left_inv {S T U : Type*}
    (e1 : ThetaLinkBi S T) (e2 : ThetaLinkBi T U) (x : S) :
    (e1.compose e2).toS ((e1.compose e2).toT x) = x :=
  (e1.compose e2).left_inv x

end LeanFormal.IUT.XiFPaper.Mzk1ThetaComposeChainActual
