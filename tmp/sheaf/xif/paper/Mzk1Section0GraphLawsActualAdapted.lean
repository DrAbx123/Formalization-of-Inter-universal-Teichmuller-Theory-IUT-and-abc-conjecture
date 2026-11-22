import tmp.sheaf.xif.paper.AbsTopIII05Section0ObjectsActual

/-!
  Mainline: Section-0 oriented-graph categorical laws (opposite/underlying, Hom
  composition, finite-linear cardinality).  Real proofs over the constructed objects.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0GraphLawsActualAdapted

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual

universe u

/-- Underlying adjacency of the opposite graph is the reversed adjacency. -/
theorem opposite_underlying_adj (G : OrientedGraph.{u}) (X Y : G.V) :
    G.opposite.underlying.Adj X Y ↔ G.underlying.Adj Y X :=
  Iff.rfl

/-- Underlying graph of the opposite is the opposite of the underlying graph. -/
theorem underlying_frobeniusPicture_adjacent (X Y : ℤ) :
    OrientedGraph.frobeniusPictureGraph.underlying.Adj X Y ↔
      LeanFormal.IUT.FrobeniusPictureArrow X Y :=
  OrientedGraph.frobeniusPictureGraph_adjacent X Y

/-- Oriented-graph morphisms map underlying adjacency forward. -/
theorem Hom.map_underlying {G H : OrientedGraph.{u}} (f : OrientedGraph.Hom G H)
    {X Y : G.V} (h : G.underlying.Adj X Y) :
    H.underlying.Adj (f.toFun X) (f.toFun Y) := by
  obtain ⟨e⟩ := h
  exact ⟨f.map e⟩

/-- Composition of oriented-graph morphisms is associative. -/
theorem Hom.comp_assoc {G H K L : OrientedGraph.{u}}
    (f : OrientedGraph.Hom G H) (g : OrientedGraph.Hom H K)
    (h : OrientedGraph.Hom K L) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  cases f
  cases g
  cases h
  rfl

/-- Identity morphisms compose neutrally. -/
theorem Hom.id_comp {G H : OrientedGraph.{u}} (f : OrientedGraph.Hom G H) :
    (OrientedGraph.Hom.id G).comp f = f := by
  cases f
  rfl

theorem Hom.comp_id {G H : OrientedGraph.{u}} (f : OrientedGraph.Hom G H) :
    f.comp (OrientedGraph.Hom.id H) = f := by
  cases f
  rfl

/-- The finite linear oriented graph has n+1 vertices. -/
theorem FinLinear_card (n : Nat) :
    Fintype.card (OrientedGraph.FinLinear n).V = n + 1 := by
  unfold OrientedGraph.FinLinear
  simp

/-- Composition acts on edge maps by function composition (rfl). -/
theorem Hom.comp_map {G H K : OrientedGraph.{u}}
    (f : OrientedGraph.Hom G H) (g : OrientedGraph.Hom H K)
    {X Y : G.V} (e : G.E X Y) :
    (f.comp g).map e = g.map (f.map e) := rfl

/-- Identity acts trivially on edge maps (rfl). -/
theorem Hom.id_map {G : OrientedGraph.{u}} {X Y : G.V} (e : G.E X Y) :
    (OrientedGraph.Hom.id G).map e = e := rfl
/-- Identity morphism acts trivially on vertices (rfl). -/
theorem Hom.id_toFun {G : OrientedGraph.{u}} (X : G.V) :
    (OrientedGraph.Hom.id G).toFun X = X := rfl

/-- Composition acts on vertices by function composition (re-export). -/
theorem Hom.comp_toFun_apply {G H K : OrientedGraph.{u}}
    (f : OrientedGraph.Hom G H) (g : OrientedGraph.Hom H K) (X : G.V) :
    (f.comp g).toFun X = g.toFun (f.toFun X) := rfl
end LeanFormal.IUT.XiFPaper.Mzk1Section0GraphLawsActualAdapted