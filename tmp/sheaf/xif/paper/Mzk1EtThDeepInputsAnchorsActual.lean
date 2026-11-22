import tmp.sheaf.xif.paper.EtTh02DeepInputsActual
import tmp.sheaf.xif.paper.Mzk1Example36EtThCorrespondenceActual
import tmp.sheaf.xif.paper.Mzk1KummerThetaInterfaceActual
import tmp.sheaf.xif.paper.Mzk1EtThRow6RealizationActual

/-!
# Mzk1EtThDeepInputsAnchorsActual — anchors for the ten [EtTh] deep paper inputs

STEP 0 prior-art: EtTh02DeepInputsActual (10 String-only named deep inputs), 
Mzk1Example36EtThCorrespondenceActual (Example36<->EtTh carrier), 
Mzk1KummerThetaInterfaceActual (Kummer/theta interface), 
Mzk1EtThRow6RealizationActual (row-6 carrier) -> REUSE; no new deep mathematics.

WHAT THIS FILE DOES:
* attaches to each of the ten EtTh deep inputs its current formalized anchor (tree asset or
  carrier-level interface) and its status, keeping every deep input NAMED (no closure claim);
* proves the id linkage: the anchor rows are exactly the ten deep inputs of EtTh02.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1EtThDeepInputsAnchorsActual

open LeanFormal.IUT.XiFPaper.EtTh02DeepInputsActual
open LeanFormal.IUT.XiFPaper.Mzk1Example36EtThCorrespondenceActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerThetaInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1EtThRow6RealizationActual

/-- One [EtTh] deep input with its current formalized anchor and status. -/
structure EtThDeepInputAnchor where
  id : String
  /-- the paper statement id (same id as EtTh02DeepInputsActual). -/
  paperId : String
  /-- the current formalized anchor (tree asset / interface / none). -/
  anchor : String
  /-- NAMED / CARRIER-LEVEL / TREE-ASSET. -/
  status : String

/-- The ten [EtTh] deep inputs with anchors (all remain NAMED; anchors are carrier-level or
tree assets, never proofs of the paper statement). -/
def etThDeepInputAnchors : List EtThDeepInputAnchor :=
  [ ⟨"EtTh.Prop1.1", "EtTh.Prop1.1", "theta group quotient interface (EtaleThetaQuotient) + ThetaQuotientInterface (IKT)", "NAMED (carrier-level interface)"⟩
  , ⟨"EtTh.Lemma1.2", "EtTh.Lemma1.2", "EtaleThetaQuotient compatibility lemmas (thetaToElliptic_mk etc.)", "NAMED (carrier-level)"⟩
  , ⟨"EtTh.Prop1.3", "EtTh.Prop1.3", "AbsoluteKummerInjection/Continuity/Quotient (etale theta class side)", "NAMED (carrier-level)"⟩
  , ⟨"EtTh.Prop1.4", "EtTh.Prop1.4", "Example36 analytic theta carrier / jacobiThetaQ / qExpansionTerm (X1)", "NAMED (analytic model)"⟩
  , ⟨"EtTh.Prop1.5", "EtTh.Prop1.5", "SourceThetaPilotIQContainment + thetaPilotPacketRows (TPI)", "NAMED (carrier-level)"⟩
  , ⟨"EtTh.Thm1.6", "EtTh.Thm1.6", "tempered anabelian rigidity: no asset", "NAMED (deep)"⟩
  , ⟨"EtTh.Thm1.10", "EtTh.Thm1.10", "constant multiple rigidity: no asset", "NAMED (deep)"⟩
  , ⟨"EtTh.Prop3.2", "EtTh.Prop3.2", "Example36 Frobenioid source model / concrete boundary (EtTh05 + X1)", "NAMED (carrier-level)"⟩
  , ⟨"EtTh.Prop3.4", "EtTh.Prop3.4", "Example36 SourceThetaDivisor/Generator (analytic theta data)", "NAMED (analytic model)"⟩
  , ⟨"EtTh.Sec4", "EtTh.Sec4", "bi-Kummer theory: no asset (AbsoluteKummer layer only)", "NAMED (deep)"⟩ ]

/-- The anchor rows are exactly the ten [EtTh] deep inputs (id linkage). -/
theorem etThDeepInputAnchors_ids_eq :
    etThDeepInputAnchors.map (fun a => a.paperId) = etThDeepInputs.map (fun d => d.id) := rfl

/-- The anchor row record has ten rows. -/
theorem etThDeepInputAnchors_length : etThDeepInputAnchors.length = 10 := rfl

#check EtThDeepInputAnchor
#check etThDeepInputAnchors_ids_eq
#check etThDeepInputAnchors_length

end LeanFormal.IUT.XiFPaper.Mzk1EtThDeepInputsAnchorsActual
end
