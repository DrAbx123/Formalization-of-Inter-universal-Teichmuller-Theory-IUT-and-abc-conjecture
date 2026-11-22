import tmp.sheaf.xif.paper.AbsTopIII05ReconstructionInputsActual
import tmp.sheaf.xif.paper.AbsTopIII05RefinedActual
import tmp.sheaf.xif.paper.Mzk1Prop58iConcreteActual
import tmp.sheaf.xif.paper.Mzk1Prop58iiDiagramActual

/-!
# Mzk1AbsTopIII05DeepInputsRefinedActual — refinement map from the four named AbsTopIII05
deep inputs to their concrete/refined anchors

STEP 0 prior-art: AbsTopIII05ReconstructionInputsActual (four String-only DeepInput rows),
AbsTopIII05RefinedActual (typed D1-D4 interfaces), Mzk1Prop58iConcreteActual (Prop 5.8(i)
concrete invariants), Mzk1Prop58iiDiagramActual (Prop 5.8(ii) concrete diagram model and
D^bullet row record) -> REUSE; no new deep mathematics.

WHAT THIS FILE DOES:
* defines the refinement map from each original DeepInput (kind prop58i / prop58ii / cor55 /
  orientedGraph) to its concrete/refined anchor asset and the remaining named part;
* proves the kind linkage (the four original kinds are exactly the four refined kinds);
* records which parts are now concrete/proved and which stay NAMED (the group-theoretic
  algorithms, the Gamma^x_non diagram, the D^bullet construction).
This is a statement-layer refinement record, not a proof of the paper's anabelian inputs.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1AbsTopIII05DeepInputsRefinedActual

open LeanFormal.IUT.XiFPaper.AbsTopIII05ReconstructionInputsActual
open LeanFormal.IUT.XiFPaper.AbsTopIII05RefinedActual
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iConcreteActual
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iiDiagramActual

/-- The refined anchor for one original deep-input kind: (concrete/refined anchor, remaining
named part). -/
def refinedAnchor : DeepInputKind → String × String
  | .prop58i => ("Prop58iConcreteInvariants + Prop58iLocalFieldReconstruction (D1)", "group-theoretic reconstruction algorithm / G_k,G_ab embeddings / Verlangerung")
  | .prop58ii => ("Prop58iiDiagramObject (concrete model vertices) + Prop58iiLogShellReconstruction (D2)", "Gamma^x_non diagram in CMLF_TF^+ / functorial algorithm")
  | .cor55 => ("preLogShell⊆unitLayer, unitLayer⊆logShell, logShell=invScaledUnitLayer (under bridge h) + Cor55LogFrobeniusCompatibility (D3)", "D^bullet seven-row diagram / global-panalocal compatibility")
  | .orientedGraph => ("frobeniusPictureGraph + FrobeniusPictureGraphAut/chainTranslation (Z-action) + OrientedGraphAnabelianData (D4)", "general combinatorial anabelian data")

/-- The refined anchor of each original DeepInput row. -/
def refinedAnchors : List (String × String × String) :=
  [ ("prop58i", (refinedAnchor .prop58i).1, (refinedAnchor .prop58i).2)
  , ("prop58ii", (refinedAnchor .prop58ii).1, (refinedAnchor .prop58ii).2)
  , ("cor55", (refinedAnchor .cor55).1, (refinedAnchor .cor55).2)
  , ("orientedGraph", (refinedAnchor .orientedGraph).1, (refinedAnchor .orientedGraph).2) ]

/-- The four original deep inputs are exactly the four refined kinds (rfl linkage). -/
theorem absTopIIIDeepInputs_kinds_eq_refined :
    absTopIIIDeepInputs.map (fun d => d.kind) =
      [.prop58i, .prop58ii, .cor55, .orientedGraph] := rfl

/-- The refined anchor record has four rows (one per original deep input). -/
theorem refinedAnchors_length : refinedAnchors.length = 4 := rfl

/-- Refinement status rows: (deep input, concrete/refined part, remaining named part). -/
def deepInputRefinementRows : List (String × String × String) :=
  [ ("D1 Prop 5.8(i)", "concrete invariants (p,p*,p^f,[k:Qp],e,p^m; unit/invariant images) + typed D1", "group-theoretic algorithm NAMED"),
    ("D2 Prop 5.8(ii)", "concrete model vertices (CMLFCarrier/NonDiagramModel) + typed D2", "Gamma^x_non diagram + functorial algorithm NAMED"),
    ("D3 Cor 5.5", "bridge consequences + typed D3 (tree calibration anchor)", "D^bullet diagram/global-panalocal compatibility NAMED"),
    ("D4 Section-0 oriented graph", "Z-graph real object + tree Z-action + typed D4 concrete instance", "general combinatorial anabelian data NAMED") ]

/-- The deep-input refinement row record has four rows. -/
theorem deepInputRefinementRows_length : deepInputRefinementRows.length = 4 := rfl

#check refinedAnchor
#check refinedAnchors_length
#check absTopIIIDeepInputs_kinds_eq_refined
#check deepInputRefinementRows_length

end LeanFormal.IUT.XiFPaper.Mzk1AbsTopIII05DeepInputsRefinedActual
end
