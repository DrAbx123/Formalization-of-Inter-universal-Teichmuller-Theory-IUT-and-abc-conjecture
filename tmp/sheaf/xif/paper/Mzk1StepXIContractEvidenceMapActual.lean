/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HolomorphicHullLogVolumeReconciliationActual
import Mathlib.Tactic

/-! # AUDIT/GAP: StepXIContract evidence map

The contract has no fields carrying evidence for hull/det/logVolumeComparison; this file
records the three obligations and their current evidence status as named audit data.
It does NOT discharge the comparison.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIContractEvidenceMapActual

inductive Obligation
  | holomorphicHull
  | determinantNormalization
  | logVolumeComparison
  deriving DecidableEq, Repr

structure EvidenceEntry where
  obligation : Obligation
  representation : String
  status : String
  evidence : String

def currentEvidence : List EvidenceEntry :=
  [ { obligation := .holomorphicHull,
      representation := "WallObligation.holomorphicHull",
      status := "NOT-DISCHARGED",
      evidence := "HullDeterminantLogVolumeReduction interface; paper carrier realization not proved" },
    { obligation := .determinantNormalization,
      representation := "WallObligation.determinantNormalization",
      status := "INTERFACE-ONLY",
      evidence := "det identities green; (Ob3-3) source identification not proved; C3-S1902 named-data interface only" },
    { obligation := .logVolumeComparison,
      representation := "WallObligation.logVolumeComparison",
      status := "PENDING",
      evidence := "S3137 q/theta raw readings green; comparison not proved" } ]

theorem currentEvidence_length : currentEvidence.length = 3 := rfl

theorem comparison_not_discharged :
    (currentEvidence.find? (fun e => e.obligation == .logVolumeComparison)).map
      (fun e => e.status) = some "PENDING" := rfl

def rows : List (String × String) :=
  [ ("holomorphicHull", "NOT-DISCHARGED"),
    ("determinantNormalization", "INTERFACE-ONLY"),
    ("logVolumeComparison", "PENDING") ]

theorem rows_length : rows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1StepXIContractEvidenceMapActual

end