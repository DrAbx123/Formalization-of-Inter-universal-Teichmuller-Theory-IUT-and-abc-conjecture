import tmp.sheaf.xif.paper.AbsTopIII05Section0ObjectsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1Section0OppositeLawsV2ActualAdapted (adapted copy, A475 reuse) — opposite-graph laws (fresh corrected path)

Adapts the EXIT1 Mzk1Section0OppositeLawsActual (rewrite-motive failure): proves
the opposite adjacency law, double-opposite equality, finite-linear instance and the
Frobenius-picture identification by explicit Iff.trans rather than rewriting.
No new math; no closure; gate NOT PASSED; registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0OppositeLawsV2ActualAdapted

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual

universe u

theorem opposite_underlying_adj {G : OrientedGraph.{u}} (X Y : G.V) :
    G.opposite.underlying.Adj X Y ↔ G.underlying.Adj Y X := Iff.rfl

theorem opposite_opposite_underlying_adj (G : OrientedGraph.{u}) :
    (G.opposite.opposite).underlying.Adj = G.underlying.Adj := by
  funext X Y
  apply propext
  exact Iff.rfl

theorem FinLinear_opposite_underlying_adj (n : Nat)
    {X Y : (OrientedGraph.FinLinear n).V} :
    (OrientedGraph.FinLinear n).opposite.underlying.Adj X Y ↔
      (OrientedGraph.FinLinear n).underlying.Adj Y X :=
  opposite_underlying_adj X Y

theorem frobeniusPicture_opposite_underlying_adj (X Y : ℤ) :
    OrientedGraph.frobeniusPictureGraph.opposite.underlying.Adj X Y ↔
      LeanFormal.IUT.FrobeniusPictureArrow Y X :=
  (opposite_underlying_adj (G := OrientedGraph.frobeniusPictureGraph) X Y).trans
    (OrientedGraph.frobeniusPictureGraph_adjacent Y X)

def section0OppositeRows : List (String × String × String) :=
  [ ("opposite adjacency", "opposite_underlying_adj", "PROVED"),
    ("double opposite", "opposite_opposite_underlying_adj", "PROVED"),
    ("FinLinear instance", "FinLinear_opposite_underlying_adj", "PROVED"),
    ("Frobenius picture", "frobeniusPicture_opposite_underlying_adj", "PROVED"),
    ("scope", "no new math; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem section0OppositeRows_length : section0OppositeRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Section0OppositeLawsV2ActualAdapted

end
