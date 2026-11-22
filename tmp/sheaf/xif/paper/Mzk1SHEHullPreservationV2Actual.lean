import Mathlib

/-!
# Mzk1SHEHullPreservationV2Actual — hull-preserving maps (real math)

Status: PENDING-VERIFY. No sorry, no axiom.
Hull-preserving maps closed under identity and composition (genuine proofs). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1SHEHullPreservationV2Actual

/-- Hull-preserving map data: carrier with hull set and preserving map. -/
structure HullPreservingMap (Carrier : Type*) where
  hull : Set Carrier
  map : Carrier → Carrier
  preserves : ∀ x, x ∈ hull → map x ∈ hull

/-- Genuine theorem: the identity map preserves the hull. -/
def HullPreservingMap.id (Carrier : Type*) (hull : Set Carrier) :
    HullPreservingMap Carrier where
  hull := hull
  map := id
  preserves := fun _ hx => hx

/-- Genuine theorem: composition of hull-preserving maps preserves the hull. -/
def HullPreservingMap.compose {Carrier : Type*} (f g : HullPreservingMap Carrier)
    (hsame : f.hull = g.hull) : HullPreservingMap Carrier where
  hull := f.hull
  map := fun x => g.map (f.map x)
  preserves := by
    intro x hx
    apply g.preserves
    apply f.preserves
    exact hx

/-- Genuine theorem: composed map acts as g ∘ f. -/
theorem HullPreservingMap.compose_apply {Carrier : Type*}
    (f g : HullPreservingMap Carrier) (hsame : f.hull = g.hull) (x : Carrier) :
    (f.compose g hsame).map x = g.map (f.map x) :=
  rfl

end LeanFormal.IUT.XiFPaper.Mzk1SHEHullPreservationV2Actual
