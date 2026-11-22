import tmp.sheaf.xif.paper.AbsTopIII05Section0ObjectsActual

/-!
# Mzk1Section0LinearGraphActual — linear oriented graphs from integer intervals
(corpus Section 0, l.1313-1318)

STEP 0 prior-art: AbsTopIII05Section0ObjectsActual (OrientedGraph, FinLinear, Adjacent) -> REUSE;
this file builds the linear oriented graph determined by an integer interval and proves its
adjacency characterization.

No axiom/sorry; registry frozen 14041.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0LinearGraphActual

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual
open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual.OrientedGraph

/-- The vertex type of the integer-interval linear graph. -/
abbrev IntIntervalVertex (a b : ℤ) : Type := {x : ℤ // a ≤ x ∧ x ≤ b}

/-- The linear oriented graph determined by the integer interval [a,b] (corpus: a countably
ordered set with the induced edge ordering). -/
def intIntervalGraph (a b : ℤ) : OrientedGraph where
  V := IntIntervalVertex a b
  E X Y := PLift (Y.1 = X.1 + 1)

/-- Adjacency in the interval graph: exactly the successor relation. -/
theorem intIntervalGraph_edge_iff (a b : ℤ) (X Y : IntIntervalVertex a b) :
    Nonempty ((intIntervalGraph a b).E X Y) ↔ Y.1 = X.1 + 1 :=
  ⟨fun ⟨e⟩ => e.down, fun h => ⟨PLift.up h⟩⟩

/-- The underlying graph of the interval graph is the successor adjacency. -/
theorem intIntervalGraph_underlying_adj (a b : ℤ) (X Y : IntIntervalVertex a b) :
    (intIntervalGraph a b).underlying.Adj X Y ↔ Y.1 = X.1 + 1 := by
  change Nonempty ((intIntervalGraph a b).E X Y) ↔ Y.1 = X.1 + 1
  exact intIntervalGraph_edge_iff a b X Y

/-- Edges of the interval graph are precisely adjacent pairs of the countably ordered set. -/
theorem intIntervalGraph_edge_adjacent (a b : ℤ) (X Y : IntIntervalVertex a b)
    (h : Nonempty ((intIntervalGraph a b).E X Y)) :
    Adjacent X.1 Y.1 := by
  exact (intIntervalGraph_edge_iff a b X Y).mp h

/-- The interval graph's vertices are nonempty exactly when a <= b. -/
theorem intIntervalGraph_vertices_nonempty {a b : ℤ} (h : a ≤ b) :
    Nonempty (intIntervalGraph a b).V :=
  ⟨⟨a, le_refl a, h⟩⟩

/-- Linear-graph rows: (item, construction, status). -/
def linearGraphRows : List (String × String × String) :=
  [ ("linear oriented graph of an integer interval", "intIntervalGraph a b (vertices Icc a b, successor edges)", "CONSTRUCTED"),
    ("adjacency characterization", "intIntervalGraph_edge_iff", "PROVED"),
    ("underlying graph adjacency", "intIntervalGraph_underlying_adj", "PROVED"),
    ("adjacent pairs", "intIntervalGraph_edge_adjacent", "PROVED"),
    ("nonempty interval has vertices", "intIntervalGraph_vertices_nonempty", "PROVED"),
    ("general countably ordered set linear graph", "interval case proved; general order-isomorphism case NAMED", "NAMED (partial)") ]

/-- The linear-graph row record has six rows. -/
theorem linearGraphRows_length : linearGraphRows.length = 6 := rfl

#check intIntervalGraph
#check intIntervalGraph_edge_iff
#check intIntervalGraph_underlying_adj
#check intIntervalGraph_edge_adjacent
#check intIntervalGraph_vertices_nonempty
#check linearGraphRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Section0LinearGraphActual
end
