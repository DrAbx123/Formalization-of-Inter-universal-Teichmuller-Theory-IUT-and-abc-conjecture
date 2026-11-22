/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.OrigXiFPaperQPilotObjectActual
import Mathlib.Tactic

/-! # A1065/A1070: Route A scalar q-pilot volume identities -/

/-
| field | value |
|---|---|
| Status | PARTIAL (scalar identities PROVED; source-root identification is GAP) |
| 真证 | `sourceQPilotSignedLog_eq_neg_badQ`; `qPilotVolumeScalarTarget_iff_badQ`; `qPilotVolumeScalarTarget_of_badQ` |
| 备注 | `S3050Unit_eq_log_norm_div` 已移到 `Mzk1S3050UnitScalarActual.lean`（避免 OrigXiF/Preorder import 冲突） |
| GAP | GAP-SOURCE-ROOT / GAP-S2691 / GAP-S3016 详见 coord/ROUTE-A-SCALAR.md |
| 循环性 | no target assumed |
-/

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.OrigXiF

namespace LeanFormal.IUT.XiFPaper.Mzk1QPilotVolumeScalarActual

variable {l : PrimeGeFive}

/-- Scalar q-pilot volume target: the source signed log-volume equals `-A`. -/
def QPilotVolumeScalarTarget (S : SourceDefinition31Data l) (A : Real) : Prop :=
  sourceQPilotSignedLog S = -A

/-- Port of the source scalar identity: signed log = negated bad-q absolute-log sum. -/
theorem sourceQPilotSignedLog_eq_neg_badQ (S : SourceDefinition31Data l) :
    sourceQPilotSignedLog S = -OrigXiFPaperBadQAbsLog S :=
  sourceQPilotSignedLog_eq_neg_badQAbsLog S

/-- The scalar target is exactly `badQAbsLog = A`. -/
theorem qPilotVolumeScalarTarget_iff_badQ (S : SourceDefinition31Data l) (A : Real) :
    QPilotVolumeScalarTarget S A ↔ OrigXiFPaperBadQAbsLog S = A := by
  unfold QPilotVolumeScalarTarget
  rw [sourceQPilotSignedLog_eq_neg_badQ]
  constructor <;> intro h <;> linarith

/-- A sufficient scalar form: if the bad-q sum is `A`, the target holds. -/
theorem qPilotVolumeScalarTarget_of_badQ (S : SourceDefinition31Data l) (A : Real)
    (hA : OrigXiFPaperBadQAbsLog S = A) : QPilotVolumeScalarTarget S A :=
  (qPilotVolumeScalarTarget_iff_badQ S A).mpr hA

def routeAScalarRows : List (String × String) :=
  [ ("QPilotVolumeScalarTarget", "sourceQPilotSignedLog S = -A (S2717 instance)") ,
    ("sourceQPilotSignedLog_eq_neg_badQ", "PROVED (port OrigXiF identity)") ,
    ("qPilotVolumeScalarTarget_iff_badQ", "PROVED (target <-> badQAbsLog = A)") ,
    ("qPilotVolumeScalarTarget_of_badQ", "PROVED (sufficient form)") ,
    ("S3050Unit_eq_log_norm_div", "moved to Mzk1S3050UnitScalarActual.lean") ,
    ("GAP-SOURCE-ROOT", "source qFamily vs paper logQ") ]

theorem routeAScalarRows_length : routeAScalarRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1QPilotVolumeScalarActual