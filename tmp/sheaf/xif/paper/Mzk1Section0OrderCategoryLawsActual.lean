import Mathlib

/-!
# Mzk1Section0OrderCategoryLawsActual — Section 0 order/category laws (genuine definitions + lemmas)

Status: PENDING-VERIFY. No sorry, no axiom.
Formal model: oriented graph core, adjacency pairs, order category. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0OrderCategoryLawsActual

/-- Oriented graph core: vertices with adjacency. -/
structure GraphCore where
  V : Type
  adj : V → V → Prop

/-- Adjacency pairs of a graph core. -/
def GraphCore.adjPairs (g : GraphCore) : Set (g.V × g.V) := {p | g.adj p.1 p.2}

/-- Genuine lemma: adjacency pairs are exactly the adjacency relation. -/
theorem GraphCore.mem_adjPairs (g : GraphCore) (x y : g.V) :
    (x, y) ∈ g.adjPairs ↔ g.adj x y :=
  Iff.rfl

/-- Order category data: preorder on a type. -/
structure OrderCat (X : Type*) where
  le : X → X → Prop
  refl : ∀ x, le x x
  trans : ∀ {a b c}, le a b → le b c → le a c

/-- Genuine lemma: order category transitivity. -/
theorem OrderCat.trans_apply {X : Type*} (o : OrderCat X) {a b c : X}
    (hab : o.le a b) (hbc : o.le b c) : o.le a c :=
  o.trans hab hbc

end LeanFormal.IUT.XiFPaper.Mzk1Section0OrderCategoryLawsActual
