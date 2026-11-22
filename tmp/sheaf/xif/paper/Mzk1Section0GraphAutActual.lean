import tmp.sheaf.xif.paper.AbsTopIII05Section0ObjectsActual

/-!
  Mainline: automorphism group of an oriented graph (real subgroup construction;
  the tree Frobenius-picture automorphisms embed into it).
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0GraphAutActual

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual

universe u

/-- Automorphisms of an oriented graph form a subgroup of the vertex permutations
  preserving underlying adjacency both ways (corpus l.1306-1310 automorphisms). -/
def GraphAut (G : OrientedGraph.{u}) : Subgroup (Equiv.Perm G.V) where
  carrier := {sigma | ∀ X Y : G.V,
    Nonempty (G.E X Y) ↔ Nonempty (G.E (sigma X) (sigma Y))}
  mul_mem' := by
    rintro a b ha hb X Y
    rw [Equiv.Perm.mul_apply]
    exact (hb X Y).trans (ha (b X) (b Y))
  one_mem' := by
    intro X Y
    simp
  inv_mem' := by
    intro a ha X Y
    have h := ha (a.symm X) (a.symm Y)
    simpa using h.symm

theorem mem_graphAut_iff (G : OrientedGraph.{u}) (sigma : Equiv.Perm G.V) :
    sigma ∈ GraphAut G ↔ ∀ X Y : G.V,
      Nonempty (G.E X Y) ↔ Nonempty (G.E (sigma X) (sigma Y)) :=
  Iff.rfl

/-- Every tree Frobenius-picture automorphism is an automorphism of the constructed
  oriented graph. -/
theorem frobeniusPictureGraphAut_mem (sigma : Equiv.Perm ℤ)
    (hsigma : LeanFormal.IUT.FrobeniusPictureGraphAut sigma) :
    sigma ∈ GraphAut OrientedGraph.frobeniusPictureGraph := by
  intro X Y
  rw [OrientedGraph.frobeniusPictureGraph_adjacent,
    OrientedGraph.frobeniusPictureGraph_adjacent]
  exact hsigma X Y

end LeanFormal.IUT.XiFPaper.Mzk1Section0GraphAutActual