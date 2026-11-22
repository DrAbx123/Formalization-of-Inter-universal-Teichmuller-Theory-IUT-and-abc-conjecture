/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1StepXIEvidenceUpgradeActual
import Mathlib.Tactic
/-! # GAP: StepXI schema->evidence consumer (no discharge) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIEvidenceConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIEvidenceUpgradeActual
structure EvidenceConsumer where
  obligation : String
  level : EvidenceLevel
  consumer : String
def consumers : List EvidenceConsumer :=
  [⟨"holomorphicHull", .absent, "hull consumer"⟩,
   ⟨"determinantNormalization", .interface, "det consumer"⟩,
   ⟨"logVolumeComparison", .absent, "comparison consumer"⟩]
theorem no_discharged_consumer :
    consumers.all (fun c => c.level == .discharged) = false := rfl
def rows : List String := ["hull consumer", "det consumer", "comparison consumer"]
theorem rows_length : rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1StepXIEvidenceConsumerActual
end