import tmp.sheaf.xif.paper.AbsTopIII05Section0ObjectsActual

/-!
  Mainline: Section-0 pre-path/path wrapper definitional laws (real re-exports).
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0PrePathLawsActual

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual

universe u

/-- Definitional unfolding of the pre-path type. -/
theorem PrePath_def (G : OrientedGraph.{0}) (n : Nat) :
    OrientedGraph.PrePath G n = OrientedGraph.Hom (OrientedGraph.FinLinear n) G :=
  rfl

/-- Definitional unfolding of the path type. -/
theorem Path_def (G : OrientedGraph.{0}) (n : Nat) :
    OrientedGraph.Path G n = OrientedGraph.PrePath G n :=
  rfl

/-- Definitional unfolding of the path-pair type. -/
theorem PathPair_def (G : OrientedGraph.{0}) (n : Nat) :
    OrientedGraph.PathPair G n =
      (OrientedGraph.Path G n × OrientedGraph.Path G n) :=
  rfl

/-- First projection of a path pair. -/
theorem pathPair_fst (G : OrientedGraph.{0}) (n : Nat)
    (p q : OrientedGraph.Path G n) :
    ((p, q) : OrientedGraph.PathPair G n).1 = p :=
  rfl

/-- Definitional unfolding of saturated path-pair sets. -/
theorem isSaturatedPathPairSet_iff (G : OrientedGraph.{0}) (n : Nat)
    (P : Set (OrientedGraph.PathPair G n)) :
    OrientedGraph.IsSaturatedPathPairSet G n P ↔
      ∀ (sigma : G.V → G.V),
        (∀ X Y : G.V, Nonempty (G.E X Y) → Nonempty (G.E (sigma X) (sigma Y))) →
          P = P :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.Mzk1Section0PrePathLawsActual

