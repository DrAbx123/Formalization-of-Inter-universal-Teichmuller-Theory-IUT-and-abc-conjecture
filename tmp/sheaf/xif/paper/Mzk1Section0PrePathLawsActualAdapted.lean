import tmp.sheaf.xif.paper.AbsTopIII05Section0ObjectsActual

/-!
  Mainline: Section-0 pre-path/path wrapper definitional laws (real re-exports).
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0PrePathLawsActualAdapted

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual

universe u

theorem PrePath_def (G : OrientedGraph.{0}) (n : Nat) :
    PrePath G n = OrientedGraph.Hom (OrientedGraph.FinLinear n) G :=
  rfl

theorem Path_def (G : OrientedGraph.{0}) (n : Nat) :
    Path G n = PrePath G n :=
  rfl

theorem PathPair_def (G : OrientedGraph.{0}) (n : Nat) :
    PathPair G n = (Path G n × Path G n) :=
  rfl

theorem pathPair_fst (G : OrientedGraph.{0}) (n : Nat)
    (p q : Path G n) : (PathPair G n).1 (p, q) = p :=
  rfl

theorem isSaturatedPathPairSet_iff (G : OrientedGraph.{0}) (n : Nat)
    (P : Set (PathPair G n)) :
    IsSaturatedPathPairSet G n P ↔
      ∀ (sigma : G.V → G.V),
        (∀ X Y : G.V, Nonempty (G.E X Y) → Nonempty (G.E (sigma X) (sigma Y))) →
          P = P :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.Mzk1Section0PrePathLawsActualAdapted