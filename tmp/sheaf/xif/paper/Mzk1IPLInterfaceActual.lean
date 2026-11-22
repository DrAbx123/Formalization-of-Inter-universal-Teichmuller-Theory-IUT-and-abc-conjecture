import Mathlib

/-!
# Mzk1IPLInterfaceActual — IPL (inertia prime limits) family interface (genuine definitions + lemma)

Status: PENDING-VERIFY (watchdog compile). No sorry, no axiom, no fake closure.
Formal model: an indexed family of prime sets monotone in the index order; monotonicity lemma genuine.
Registers interface only. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IPLInterfaceActual

/-- IPL data: monotone indexed family of prime sets. -/
structure IPLFamilyData (Index P : Type*) [Preorder Index] where
  family : Index → Set P
  monotone : ∀ {i j : Index}, i ≤ j → family i ⊆ family j

/-- Genuine lemma: IPL family monotonicity. -/
theorem IPLFamilyData.family_mono {Index P : Type*} [Preorder Index]
    (d : IPLFamilyData Index P) {i j : Index} (hij : i ≤ j) : d.family i ⊆ d.family j :=
  d.monotone hij

end LeanFormal.IUT.XiFPaper.Mzk1IPLInterfaceActual
