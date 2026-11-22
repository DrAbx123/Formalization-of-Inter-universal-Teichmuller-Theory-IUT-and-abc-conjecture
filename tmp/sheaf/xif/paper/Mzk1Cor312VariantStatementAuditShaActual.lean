import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import tmp.sheaf.xif.paper.Mzk1SignedCor312ContractActual
import Mathlib.Tactic

/-!
# Audit: `Cor312Conclusion` vs lana `Corollary312Variant` (field-level differences)

Two formalizations of the IUT III Corollary 3.12 shape exist on disk:
* ours: `StepXIContract` + `Cor312Conclusion` (`LeanFormal/IUT/IUTIII/Corollary312/StepXI/Contract.lean`),
  with the signed assembly `signedCor312Contract`;
* lana: `Iut.Corollary312VariantData` + `Corollary312Variant`
  (`tmp/sheaf/lana_latest/Iut/Cor312/Statement.lean`), an explicitly UNPROVED
  Prop-valued definition whose module docstring states it is not the published
  Corollary 3.12 verbatim.

This audit records the field-level differences; it does NOT claim a Lean bridge
between the two definitions (no such bridge theorem exists in the repository, and
the lana module is not compiled in this environment: olean absent).

No RETRACTED statement is used.  No sorry/axiom/True.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312VariantStatementAuditShaActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual

/-- Ours: `Cor312Conclusion` unfolds definitionally to the ordered inequality. -/
theorem ourConclusion_iff (C : StepXIContract) :
    Cor312Conclusion C ↔ C.qSigned ≤ C.thetaSigned :=
  Iff.rfl

/-- Ours: the contract already gives the conclusion (no extra hypothesis). -/
theorem ourConclusion_of_contract (C : StepXIContract) : Cor312Conclusion C :=
  cor312_of_constructed_stepXI C

/-- Ours: the signed assembly reaches the conclusion from the signed inequality. -/
theorem ourSignedConclusion
    (qSigned thetaSigned : Real) (hq : qSigned < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) (hle : qSigned ≤ thetaSigned) :
    Cor312Conclusion
      (signedCor312Contract qSigned thetaSigned hq ipl hipl she hshe apt hapt hle) :=
  signedCor312_conclusion qSigned thetaSigned hq ipl hipl she hshe apt hapt hle

structure VariantRow where
  aspect : String
  ourSide : String
  lanaSide : String
  relation : String
  deriving Repr, DecidableEq

def variantRows : List VariantRow :=
  [ ⟨"carrier data",
     "StepXIContract: qSigned/thetaSigned/targetSigned reals; ipl/she/apt as Props",
     "Corollary312VariantData: InitialThetaData + QPilotData + RHSData",
     "DIFFERENT TYPES; no map or bridge theorem in repo"⟩
  , ⟨"inequality",
     "qSigned <= thetaSigned (via targetSigned)",
     "X.qPilot.lhs <= X.rhsData.rhs (direct)",
     "same paper shape (-|log q| <= -|log Theta|), different formal data"⟩
  , ⟨"sign field",
     "q_negative : qSigned < 0 (explicit field)",
     "sign encoded in lhs/rhs and admissibility fields; no separate sign field",
     "OURS EXTRA FIELD"⟩
  , ⟨"intermediate target",
     "targetSigned with q_le_target and target_le_theta",
     "no intermediate target (direct comparison)",
     "OURS EXTRA STRUCTURE"⟩
  , ⟨"wall obligations",
     "ipl/she/apt as Props plus evidence fields",
     "assumptions are visible fields of RHSData/admissibility (textual)",
     "CORRESPONDENCE NOT FORMALIZED"⟩
  , ⟨"proof status",
     "contract -> Cor312Conclusion PROVED; contract construction from source unfinished",
     "Corollary312Variant deliberately UNPROVED (no axiom)",
     "DIFFERENT PROOF BOUNDARIES"⟩
  , ⟨"ABC link",
     "our ABC route goes through interface/estimates, not through this contract alone",
     "classicalABC_of_variant : Cor312VariantHolds -> ClassicalABC",
     "BOTH CONDITIONAL; DIFFERENT HYPOTHESES"⟩
  , ⟨"not-identification",
     "StepXIContract docstring: contracts for obligations, not Hodge theaters",
     "lana docstring: not the published Corollary 3.12 verbatim",
     "BOTH DISCLAIM IDENTIFICATION"⟩
  , ⟨"bridge",
     "no Lean theorem connecting the two definitions",
     "lana module olean absent in this environment",
     "NAMED AUDIT GAP"⟩
  ]

theorem variantRows_length : variantRows.length = 9 := rfl

theorem variantRows_has_bridge_gap :
    variantRows.any (fun r => r.relation = "NAMED AUDIT GAP") = true := by
  decide

theorem variantRows_has_different_types :
    variantRows.any (fun r => r.relation = "DIFFERENT TYPES; no map or bridge theorem in repo") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1Cor312VariantStatementAuditShaActual

/-! ### Axiom gates (our side only) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312VariantStatementAuditShaActual.ourConclusion_of_contract
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312VariantStatementAuditShaActual.ourSignedConclusion
#print axioms LeanFormal.IUT.cor312_of_constructed_stepXI
