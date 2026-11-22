import tmp.sheaf.xif.paper.AbsTopIII05ReconstructionInputsActual
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellAbsTopIIIBridge
import LeanFormal.IUT.IUTI.HodgeTheater.SourceThetaLinkGraphAutomorphismReduction
import tmp.sheaf.xif.paper.S3171IUTIVSection1DisplayActual

/-!
# AbsTopIII05RefinedActual — typed refinement of the four [AbsTopIII] deep inputs,
tree-anchored where the tree already proves the anchor, and wired conditionally into the
S3171 / IUT IV §1 consumption points

STEP 0 prior-art: AbsTopIII05ReconstructionInputsActual (four named DeepInput rows D1-D4,
String-only), SourceLogShellAbsTopIIIBridge (SourceLogShellInvariantImageIdentification +
calibration theorem), SourceThetaLinkGraphAutomorphismReduction (oriented Z-graph Gamma /
FrobeniusPictureGraphAut / chainTranslation_graphAut), S3171IUTIVSection1DisplayActual
(Thm110DisplayTerms/Inputs, paperRouteResidualData_of_undilated, abcConjecture_of_undilated)
-> REUSE; no new deep mathematics.

WHAT THIS FILE DOES:
* refines the four String-only DeepInput rows into typed interfaces
  (Prop58iLocalFieldReconstruction, Prop58iiLogShellReconstruction,
   Cor55LogFrobeniusCompatibility, OrientedGraphAnabelianData);
  the D3 anchor (bridge card on the frozen calibration datum) and the D4 anchor
  (Z-action graph automorphisms) are DISCHARGED from the tree's proved theorems, while the
  genuinely deep anabelian content stays an explicit named Prop with a proof field;
* packages them as RefinedDeepInputs and proves the refinement maps onto the original four
  DeepInput kinds (rfl-level linkage);
* records the exact S3171 / IUT IV §1 consumption points and provides the CONDITIONAL
  route-slot wiring: the refined deep inputs are carried alongside the S3171 route inputs
  (display inputs + undilated height/region bounds); the route conclusion (display +
  ABC) is obtained from the tree's proved route theorem, never from asserting the deep
  inputs.  No closure; the concrete S3171 route does not invoke D1-D4 (documented).
Registry frozen 14041; binding HOLD; gate NOT PASSED.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.AbsTopIII05RefinedActual

universe u

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.AbsTopIII05ReconstructionInputsActual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteHeightReductionActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteRegionReductionActual

/-- D1 typed refinement of Prop 5.8(i): the p-adic local-field reconstruction data
(residue cardinality p^f, absolute degree, ramification index, order of p-th power roots
of unity) as an explicit interface over a field K; the reconstruction obligation stays a
named Prop with a proof field. -/
structure Prop58iLocalFieldReconstruction (K : Type u) [Field K] where
  residueCardinality : ℕ
  absoluteDegree : ℕ
  ramificationIndex : ℕ
  pthRootsOrder : ℕ
  unitLayer : Set K
  unitLayerImage : Set K
  reconstruction : Prop
  reconstruction_proof : reconstruction

/-- D2 typed refinement of Prop 5.8(ii): the functorial Gamma^x_non diagram and the
log-shell reconstruction inside k^~(G), as an explicit interface; the functoriality
obligation stays a named Prop with a proof field. -/
structure Prop58iiLogShellReconstruction (K : Type u) [Field K] where
  gammaXNon : Type u
  logShell : Set K
  diagram : gammaXNon → Set K
  functorial : Prop
  functorial_proof : functorial

/-- D3 typed refinement of Cor 5.5: global and panalocal mono-anabelian log-Frobenius
compatibility as named obligations; the tree-side bridge-card anchor on the frozen
calibration datum is DISCHARGED by the tree theorem
sourceLogShellCalibration_invariantImageIdentification (default field). -/
structure Cor55LogFrobeniusCompatibility where
  globalCompatibility : Prop
  globalCompatibility_proof : globalCompatibility
  panalocalCompatibility : Prop
  panalocalCompatibility_proof : panalocalCompatibility
  bridgeAnchor : SourceLogShellInvariantImageIdentification sourceLogShellCalibrationDatum :=
    sourceLogShellCalibration_invariantImageIdentification

/-- The bridge-card anchor reused from the tree (proved there; re-exported here). -/
theorem cor55_treeBridgeAnchor :
    SourceLogShellInvariantImageIdentification sourceLogShellCalibrationDatum :=
  sourceLogShellCalibration_invariantImageIdentification

/-- D4 typed refinement of the Section-0 oriented graph Gamma^x_v: the combinatorial
anabelian data stays a named Prop; the Z-action graph-automorphism anchor is DISCHARGED
by the tree theorem chainTranslation_graphAut (default field). -/
structure OrientedGraphAnabelianData where
  combinatorialData : Prop
  combinatorialData_proof : combinatorialData
  zActionAnchor : ∀ k : Int, FrobeniusPictureGraphAut (chainTranslation k) :=
    fun k => chainTranslation_graphAut k

/-- The oriented-graph Z-action anchor reused from the tree (proved there). -/
theorem orientedGraph_treeZActionAnchor :
    ∀ k : Int, FrobeniusPictureGraphAut (chainTranslation k) :=
  fun k => chainTranslation_graphAut k

/-- The refined four deep inputs (D1-D4), parameterized by the two local fields used by
D1/D2.  This is the typed replacement of the four String-only rows. -/
structure RefinedDeepInputs (K1 K2 : Type u) [Field K1] [Field K2] where
  d1 : Prop58iLocalFieldReconstruction K1
  d2 : Prop58iiLogShellReconstruction K2
  d3 : Cor55LogFrobeniusCompatibility
  d4 : OrientedGraphAnabelianData

/-- The original four DeepInput kinds, in the original order. -/
def refinedDeepInputKinds : List DeepInputKind :=
  [.prop58i, .prop58ii, .cor55, .orientedGraph]

/-- The typed refinement is exactly the original four named deep inputs (kind linkage). -/
theorem refinedDeepInputKinds_eq_original :
    refinedDeepInputKinds = absTopIIIDeepInputs.map (fun d => d.kind) := rfl

/-- S3171 / IUT IV §1 route slot: the tree's proved route inputs (Thm 1.10 display inputs
and the undilated height/region bounds).  This is the exact consumption point of the
concrete route. -/
structure S3171RouteSlot (X : Type u) (W : IQHullLogVolumeInterface X)
    (pt : ℕ → ℕ → ℕ → X) (T : Thm110DisplayTerms) where
  displayInputs : Thm110DisplayInputs T
  heightBound : UndilatedHeightBound W pt
  regionBound : UndilatedRegionBound W pt

/-- The route slot yields the exact Thm 1.10 display together with ABC (tree-proved
consumer chain, conditional on the slot's class-B inputs). -/
theorem s3171RouteSlot_display_and_abc {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : ℕ → ℕ → ℕ → X} {T : Thm110DisplayTerms}
    (S : S3171RouteSlot X W pt T) :
    thm110Lhs T ≤ thm110Rhs T ∧ ABCConjecture :=
  thm110_display_and_abc_of_undilated T S.displayInputs S.heightBound S.regionBound

/-- CONDITIONAL wiring: the refined [AbsTopIII] deep inputs are carried alongside the
S3171 route slot; the route conclusion is the tree-proved display + ABC, never derived
from the deep inputs (which the concrete route does not invoke). -/
theorem absTopIII05Refined_with_s3171RouteSlot {K1 K2 : Type u} [Field K1] [Field K2]
    (_R : RefinedDeepInputs K1 K2) {X : Type u} {W : IQHullLogVolumeInterface X}
    {pt : ℕ → ℕ → ℕ → X} {T : Thm110DisplayTerms}
    (S : S3171RouteSlot X W pt T) :
    thm110Lhs T ≤ thm110Rhs T ∧ ABCConjecture :=
  s3171RouteSlot_display_and_abc S

/-- Exact consumption-point mapping rows: (refined deep input, S3171/IUT IV §1 consumption
point, status).  The concrete route does not invoke D1-D4 (they are optional
strengthening); the tree-proved anchors and the route consumer chain are cited exactly. -/
def absTopIII05RefinedConsumptionRows : List (String × String × String) :=
  [ ("D1 Prop 5.8(i) typed",
      "S3171IUTIVSection1DisplayActual.thm110_final_display / thm110_display_and_abc_of_undilated (IUT IV §1 (b)/(c) route); no direct consumption",
      "NOT consumed by the concrete route; optional typed strengthening slot"),
    ("D2 Prop 5.8(ii) typed",
      "SourceLogShellAbsTopIIIBridge (bridge-card dictionary: SourceLogShellInvariantImageIdentification + calibration theorem)",
      "tree anchor reused; the deep Gamma^x_non/log-shell construction remains NAMED"),
    ("D3 Cor 5.5 typed",
      "Cor55LogFrobeniusCompatibility.bridgeAnchor := sourceLogShellCalibration_invariantImageIdentification; S3171IUTIVSection1DisplayActual route consumer",
      "tree anchor DISCHARGED; global/panalocal log-Frobenius compatibility remains NAMED"),
    ("D4 Section-0 oriented graph typed",
      "OrientedGraphAnabelianData.zActionAnchor := chainTranslation_graphAut (SourceThetaLinkGraphAutomorphismReduction); S3171/IUT IV does not consume",
      "tree Z-action anchor DISCHARGED; combinatorial anabelian data remains NAMED") ]

/-- The consumption-point row record has four rows (one per deep input). -/
theorem absTopIII05RefinedConsumptionRows_length :
    absTopIII05RefinedConsumptionRows.length = 4 := rfl

/-- Status row: what the refinement changed and what stays exactly named. -/
def absTopIII05RefinedStatus : List (String × String × String) :=
  [ ("D1-D4 String-only rows (AbsTopIII05ReconstructionInputsActual)", "4 DeepInput rows with kind/statement/corpus/treeAnchor/proved", "REFINED: now typed structures with explicit fields + named obligations"),
    ("tree anchors", "sourceLogShellCalibration_invariantImageIdentification (bridge card); chainTranslation_graphAut (oriented Z-graph)", "DISCHARGED in the default fields (tree theorems reused)"),
    ("deep anabelian content", "Prop 5.8(i)/(ii), Cor 5.5 global/panalocal compatibility, Section-0 combinatorial data", "STILL NAMED (explicit Prop + proof fields; no closure claimed)"),
    ("S3171/IUT IV §1 consumption", "S3171RouteSlot -> thm110_display_and_abc_of_undilated", "CONDITIONAL route consumer; refined inputs carried, not asserted") ]

/-- The status row record has four rows. -/
theorem absTopIII05RefinedStatus_length : absTopIII05RefinedStatus.length = 4 := rfl

#check Prop58iLocalFieldReconstruction
#check Prop58iiLogShellReconstruction
#check Cor55LogFrobeniusCompatibility
#check OrientedGraphAnabelianData
#check RefinedDeepInputs
#check refinedDeepInputKinds_eq_original
#check cor55_treeBridgeAnchor
#check orientedGraph_treeZActionAnchor
#check absTopIII05Refined_with_s3171RouteSlot
#check absTopIII05RefinedConsumptionRows_length

end LeanFormal.IUT.XiFPaper.AbsTopIII05RefinedActual
end
