import tmp.sheaf.xif.paper.AbsTopIII05Section0ObjectsActual

/-! Mainline: opposite-graph laws (real proofs on constructed Section-0 graphs). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0OppositeLawsActual

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual

universe u

/-- Underlying adjacency of the opposite graph is reversed adjacency. -/
theorem opposite_underlying_adj {G : OrientedGraph.{u}} (X Y : G.V) :
    G.opposite.underlying.Adj X Y ↔ G.underlying.Adj Y X := by
  change Nonempty (G.E Y X) ↔ Nonempty (G.E Y X)
  exact Iff.rfl

/-- Opposite of the opposite has the same underlying adjacency. -/
theorem opposite_opposite_underlying_adj (G : OrientedGraph.{u}) :
    (G.opposite.opposite).underlying.Adj = G.underlying.Adj := by
  funext X Y
  rfl

theorem FinLinear_opposite_underlying_adj (n : Nat)
    {X Y : (OrientedGraph.FinLinear n).V} :
    (OrientedGraph.FinLinear n).opposite.underlying.Adj X Y ↔
      (OrientedGraph.FinLinear n).underlying.Adj Y X :=
  by
  change Nonempty ((OrientedGraph.FinLinear n).E Y X) ↔
    Nonempty ((OrientedGraph.FinLinear n).E Y X)
  exact Iff.rfl

theorem frobeniusPicture_opposite_underlying_adj (X Y : ℤ) :
    OrientedGraph.frobeniusPictureGraph.opposite.underlying.Adj X Y ↔
      LeanFormal.IUT.FrobeniusPictureArrow Y X := by
  change Nonempty (OrientedGraph.frobeniusPictureGraph.E Y X) ↔
    LeanFormal.IUT.FrobeniusPictureArrow Y X
  exact OrientedGraph.frobeniusPictureGraph_adjacent Y X

end LeanFormal.IUT.XiFPaper.Mzk1Section0OppositeLawsActual

