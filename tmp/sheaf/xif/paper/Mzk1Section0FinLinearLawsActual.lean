import tmp.sheaf.xif.paper.AbsTopIII05Section0ObjectsActual

/-!
  Mainline: finite linear oriented graph edge laws (real proofs).
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0FinLinearLawsActual

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual

theorem FinLinear_edge_iff (n : Nat) {X Y : (OrientedGraph.FinLinear n).V} :
    Nonempty ((OrientedGraph.FinLinear n).E X Y) ↔ Y.val = X.val + 1 :=
  ⟨fun ⟨e⟩ => e.down, fun h => ⟨PLift.up h⟩⟩

theorem FinLinear_edge_forward (n : Nat) {X Y : (OrientedGraph.FinLinear n).V}
    (h : Nonempty ((OrientedGraph.FinLinear n).E X Y)) : X.val < Y.val := by
  obtain ⟨e⟩ := h
  have hY : Y.val = X.val + 1 := e.down
  omega

theorem FinLinear_edge_irrefl (n : Nat) (X : (OrientedGraph.FinLinear n).V) :
    ¬ Nonempty ((OrientedGraph.FinLinear n).E X X) := by
  intro h
  have := FinLinear_edge_forward n h
  omega

theorem FinLinear_vertex_lt_succ (n : Nat) (X : (OrientedGraph.FinLinear n).V) :
    X.val < n + 1 := X.isLt

end LeanFormal.IUT.XiFPaper.Mzk1Section0FinLinearLawsActual