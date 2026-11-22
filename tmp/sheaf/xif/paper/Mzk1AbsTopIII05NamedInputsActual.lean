import tmp.sheaf.xif.paper.AbsTopIII05ReconstructionInputsActual
import tmp.sheaf.xif.paper.AbsTopIII05RefinedActual
import tmp.sheaf.xif.paper.Mzk1AbsTopIII05DeepInputsRefinedActual

/-!
# Mzk1AbsTopIII05NamedInputsActual — the four AbsTopIII05 deep inputs (D1-D4) as explicit
named hypotheses, with the refinement map

STEP 0 prior-art: AbsTopIII05ReconstructionInputsActual (four statements),
AbsTopIII05RefinedActual (typed D1-D4), Mzk1AbsTopIII05DeepInputsRefinedActual (refinement
anchors) -> REUSE.
This file packages D1-D4 as explicit named hypotheses, keeps the refinement rows, and gives
the conditional consumers; the deep anabelian inputs are not proved.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1AbsTopIII05NamedInputsActual

open LeanFormal.IUT.XiFPaper.AbsTopIII05ReconstructionInputsActual
open LeanFormal.IUT.XiFPaper.AbsTopIII05RefinedActual
open LeanFormal.IUT.XiFPaper.Mzk1AbsTopIII05DeepInputsRefinedActual

/-- The four AbsTopIII05 deep inputs as explicit named hypotheses (paper statements). -/
structure AbsTopIII05NamedInputs where
  /-- D1: the paper Prop 5.8(i) reconstruction statement shape. -/
  prop58i : Prop
  /-- D2: the paper Prop 5.8(ii) Gamma^x_non diagram statement. -/
  prop58ii : Prop
  /-- D3: the paper Cor 5.5 D^bullet compatibility statement. -/
  cor55 : Prop
  /-- D4: the paper Section-0 combinatorial anabelian data statement. -/
  orientedGraph : Prop
  namedD1 : prop58i
  namedD2 : prop58ii
  namedD3 : cor55
  namedD4 : orientedGraph

/-- Conditional consumer of D1. -/
theorem absTopIII05_D1 (I : AbsTopIII05NamedInputs) : I.prop58i := I.namedD1

/-- Conditional consumer of D2. -/
theorem absTopIII05_D2 (I : AbsTopIII05NamedInputs) : I.prop58ii := I.namedD2

/-- Conditional consumer of D3. -/
theorem absTopIII05_D3 (I : AbsTopIII05NamedInputs) : I.cor55 := I.namedD3

/-- Conditional consumer of D4. -/
theorem absTopIII05_D4 (I : AbsTopIII05NamedInputs) : I.orientedGraph := I.namedD4

/-- Rows: (deep input, concrete/refined anchor, status). -/
def absTopIII05NamedInputRows : List (String × String × String) :=
  [ ("D1 Prop 5.8(i)", "Prop58iConcreteInvariants + D1 typed interface; named shape in AbsTopIII05NamedInputs", "CONCRETE + NAMED"),
    ("D2 Prop 5.8(ii)", "NonDiagramModel + D2 typed interface; named shape here", "CONCRETE + NAMED"),
    ("D3 Cor 5.5", "bridge consequences + D3 typed interface; named shape here", "CONCRETE + NAMED"),
    ("D4 Section-0 oriented graph", "frobeniusPictureGraph Z-action + D4 typed interface; named shape here", "CONCRETE + NAMED"),
    ("conditional consumers", "absTopIII05_D1/2/3/4", "PROVED (conditional)") ]

/-- The named-input row record has five rows. -/
theorem absTopIII05NamedInputRows_length : absTopIII05NamedInputRows.length = 5 := rfl

#check AbsTopIII05NamedInputs
#check absTopIII05_D1
#check absTopIII05_D2
#check absTopIII05_D3
#check absTopIII05_D4
#check absTopIII05NamedInputRows_length

end LeanFormal.IUT.XiFPaper.Mzk1AbsTopIII05NamedInputsActual
end
