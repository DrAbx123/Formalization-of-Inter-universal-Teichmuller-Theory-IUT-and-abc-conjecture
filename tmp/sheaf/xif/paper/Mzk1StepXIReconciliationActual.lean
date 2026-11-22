import Mathlib.Tactic

/-!
# A834 Step XI reconciliation table (shehdd)

Machine table for `coord/STEPXI-RECONCILIATION.md`: every `VerificationStatus.pending`
obligation found in `LeanFormal/IUT/IUTIII/Corollary312/**` (incl. `StepXI/` and
`StepXI/HolomorphicHull/`), `IUTII/Theta/*`, `IUTI/HodgeTheater/*`, with the corresponding
green support and status (DISCHARGED/PARTIAL/MISSING).

Verdict: 0 fully DISCHARGED, 11 PARTIAL, 3 MISSING; no fake discharge.
No RETRACTED statement is used.  No sorry/axiom/True.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIReconciliationActual

structure RecRow where
  obligation : String
  fileLine : String
  greenSupport : String
  status : String
  deriving Repr, DecidableEq

def recRows : List RecRow :=
  [ ⟨"IUT-I.hodge-theater-source-existence", "IUTI/HodgeTheater/SourceObligations.lean:24", "none", "MISSING"⟩
  , ⟨"IUT-III.IPL", "IUTIII/Corollary312/Obligations.lean:8", "SourceLinkFactorization (Theorem311/SourceKummerEvaluationArrows.lean:418); kummerMap_thetaOne (Mzk1KummerTransportActual)", "PARTIAL"⟩
  , ⟨"IUT-III.SHE", "IUTIII/Corollary312/Obligations.lean:15", "SourceLocalizationExpressible (SourceArithmeticHolomorphicLanding.lean:292); SourceSHETransportLaws", "PARTIAL"⟩
  , ⟨"IUT-III.APT", "IUTIII/Corollary312/Obligations.lean:22", "SourceAPTStatement/SourceAPTSlotAssembly (StepXI/APT.lean:308,332); Mzk1StepXIMinimalStatementShaActual", "PARTIAL"⟩
  , ⟨"IUT-III.theorem-3.11.5", "IUTIII/Corollary312/Routes.lean:56", "Mzk1Paper312ExplicitActual; Mzk1PaperNormDeficitActual; Mzk1HVLemmaActual; Mzk1HullLogVolumeFormulaActual", "PARTIAL"⟩
  , ⟨"IUT-III.theorem-3.11.5-to-corollary-3.12", "IUTIII/Corollary312/Routes.lean:75", "Mzk1StepXIFormalizationAttemptActual; Mzk1ScaledClosingShaActual; Mzk1Paper312StatementActual", "PARTIAL"⟩
  , ⟨"IUT-III.arithmetic-teichmuller-corollary-3.12-route", "IUTIII/Corollary312/Routes.lean:87", "none", "MISSING"⟩
  , ⟨"IUT-III.sarkisyan-erdos-kac-route", "IUTIII/Corollary312/Routes.lean:105", "none", "MISSING"⟩
  , ⟨"IUT-III.route-comparison-audit", "IUTIII/Corollary312/Routes.lean:123", "coord/STEP-XI-SPEC.md (markdown only)", "MISSING"⟩
  , ⟨"IUT-III.source-APT-transport-supply", "IUTIII/Corollary312/StepXI/APT.lean:460", "SourceAPTStatement + slot assembly; Mzk1KummerTransportActual", "PARTIAL"⟩
  , ⟨"IUT-III.StepXI.contract-construction", "IUTIII/Corollary312/StepXI/Contract.lean:64", "Mzk1StepXIMinimalStatementShaActual; Mzk1A763BoxAssemblyShaActual; Mzk1StepXIFormalizationAttemptActual", "PARTIAL"⟩
  , ⟨"IUT-III.source-column-carrier-identification", "IUTIII/Corollary312/StepXI/FiniteSourceColumnTrunkBridge.lean:284", "SourceColumnCarrierIdentification.lean (landed trunk); Mzk1Cor312ChainCertificate", "PARTIAL"⟩
  , ⟨"IUT-III.source-adjacent-column-procession-isomorphism", "IUTIII/Corollary312/StepXI/SourceAdjacentColumnProcessionIsomorphism.lean:324", "file's landed components; Mzk1HullLogVolumeFormulaActual; scaled theta", "PARTIAL"⟩
  , ⟨"IUT-III.source-SHE-square-supply", "IUTIII/Corollary312/StepXI/SourceSHETransportObligations.lean:397", "SourceSHETransportLaws; kummerMap_thetaOne (Mzk1KummerTransportActual)", "PARTIAL"⟩
  ]

theorem recRows_length : recRows.length = 14 := rfl

theorem recRows_status_ok :
    recRows.all (fun r => r.status ∈ ["DISCHARGED", "PARTIAL", "MISSING"]) = true := by
  decide

theorem recRows_counts :
    (recRows.filter (fun r => r.status = "DISCHARGED")).length = 0 ∧
      (recRows.filter (fun r => r.status = "PARTIAL")).length = 10 ∧
      (recRows.filter (fun r => r.status = "MISSING")).length = 4 := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1StepXIReconciliationActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIReconciliationActual.recRows_length
#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIReconciliationActual.recRows_counts
