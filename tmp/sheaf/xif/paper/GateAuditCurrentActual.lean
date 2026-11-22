/- Gate audit snapshot: accepted components and exact open blockers after the
2026-11-16 P7-native closure and P6 IV/paper-bound work.  This file carries the
audit ledger as data; it asserts no unproved mathematics. -/
import Mathlib

noncomputable section
namespace LeanFormal.IUT.XiFPaper.GateAuditCurrentActual

/-- Accepted components at this gate (name, evidence file/decl). -/
def gateAuditAccepted : List (String × String) := 
  [ ("P7 node", "Mzk1P7NodeAssemblyDoneActual.p7_native_node_assembly (DONE 20:25:09; standard three)")
  , ("P7 SourceTorsionDatum/Clause C", "Mzk1P7SourceTorsionDatumActual.sourceTorsionDatumOfNative/sourceClauseC_of_native")
  , ("P6 StepV averages", "Mzk1P6StepVAveragesActual.p6_stepVAverages_ivInequality")
  , ("P6 IV inequality", "Mzk1P6IVActual.p6_iv_inequality")
  , ("P6 paper bound", "Mzk1P6PaperBoundActual.p6IVR_eq_paperBound")
  , ("P6 Thm110 display (generic)", "Mzk1P6Thm110DisplayActual.p6_thm110_display")
  , ("P6 IV/display assembly", "Mzk1P6IVDisplayAssemblyActual.p6_iv_display_assembly")
  , ("ABCStatement to ABCConjecture", "Mzk1ABCStatementBridgeActual.abcStatement_to_ABCConjecture")
  , ("P8 FromP6IV consumer", "Mzk1P8FromP6IVActual.p8FromP6IV_combined")
  , ("P8 FromP6IV inequality consumer", "Mzk1P8FromP6IVInequalityActual.p8UniformHeightBound_of_p6IVInequality")
  , ("H1a full node", "Mzk1H1aFullNodeActual (DONE 19:14:59; standard three)")
  , ("P5 node", "Node09P5ThetaSideFinalActual.qPilotRealifiedLogVolume_le_thetaReading")
  , ("H1b signed volume", "Node09H1bTensorVolumeActual.h1b_signed_volume_eq_relativeHaarLog")
  , ("P4 J_q/weight1", "Mzk1P4JqLatticeActual / Mzk1P4WeightedReadingClosureActual")
  ]

/-- Revoked or downgraded items and the reason. -/
def gateAuditRevoked : List (String × String) := 
  [ ("P6 DisplaySourceConstantsActual", "type inhabitant only; dFpd/fFpd = S2990 constants are not paper dF_tpd/fF_tpd (S2959CThetaParameterAuditActual)")
  , ("P6 DisplaySourceActual", "same provenance issue as above")
  , ("Mzk1CThetaUpperActual", "toy: dFpd=1/dmod=eStar=etaPrm=0 and fFpd fitted to target B")
  , ("Mzk1P7GapMarginActual", "PaperKummerReading field unpacking; replaced by Mzk1P7GapActualActual (P5 actual inequality)")
  , ("P6 StepVBoundActual", "process crash 4294967295; use StepVBoundConsumerActual/StepV averages instead")
  ]

/-- Exact open blockers at this gate. -/
def gateAuditOpenBlockers : List String := 
  [ "paper CTheta six parameters: S2959LogQAt/DmodAt/DFpdAt/FFpdAt/EStarAt/EtaPrmAt + S2959CThetaPaper_source_eq missing"
  , "P8UniformHeightBound: actual FreHeight producer (forall eps>0, FreyHeightBound eps) still ABC-level open"
  , "G1 node: actual FreyHeightBoundAll producer still open"
  , "P6 hCor312 supply: needs actual S2953CThetaUpperCertificate with paper parameters"
  , "P8UniformHeightInput: P8P6IVInequalityInput is equivalent to ABC, not constructed"
  ]

theorem gateAuditAccepted_length : gateAuditAccepted.length = 14 := rfl
theorem gateAuditRevoked_length : gateAuditRevoked.length = 5 := rfl
theorem gateAuditOpenBlockers_length : gateAuditOpenBlockers.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.GateAuditCurrentActual
end
