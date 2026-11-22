/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A638 hull: Gogopex Stage1 Cor 3.12 audit (statement-only; no external import)

Textual audit of `tmp/online/Gogopex__iut-lean/iut-lean-master`:

* `Iut/Stage1/CorollarySchema.lean` (198 lines): the schema
  `Corollary312Inequality (theta q : PilotLogVolume) := -theta.value >= -q.value`;
  `signedPilotLogVolume side s := {side, value := -s}`;
  `corollary312_of_signed_le (hle : qSigned <= thetaSigned) :
     Corollary312Inequality (signed theta) (signed q)` is proved by `linarith`;
  `Corollary312ComparisonData` takes `q_positive : 0 < -qSigned` and
  `qSigned_le_thetaSigned : qSigned <= thetaSigned` as FIELDS.  Hence the schema
  files assume the signed inequality; they do not prove IUT III Corollary 3.12.
* `Iut/Stage1/IUTSourceScaffold.lean` (108 lines):
  `SourceObligationLedger` records certified output, structured certificate
  (IPL/SHE/APT), charted container, q-value, theta-bound, common bound,
  target volume, membership, q_positive, normalization as FIELDS; its theorem
  `qSigned_le_thetaSigned` is derived from `membership.q_le_target` and
  `choiceTargetVolume_le_of_commonBound`; the ledger is an explicit hypothesis.
* `Iut/Stage1/IUTStage1Source.lean` (54,738 lines, 0 `sorry`, 0 `axiom`):
  a *source-obligation ledger plumbing* file (2,383 theorems, 772 `obligation`
  occurrences) whose endpoints are audit equalities (`rfl`, `Subsingleton.elim`)
  over the ledger structures; the actual IUT III inputs remain fields of
  `SourceObligationLedger` / `IUTStage1Theorem311StructuredInputs` /
  `IUTStage1SourceSideConditionHypotheses`, not proved there.
* `Iut/Stage1/IUTStage1Remark312Absorption.lean`: Remark 3.12.2(v) shadows
  (`ZeroColumnHullAbsorbsUnitIndeterminacy` / `OneColumnLogVolumeCompatibility`)
  with bounds/equalities as data fields.

Conclusion: the Gogopex line is a *conditional schema*
`SourceObligationLedger -> Corollary312Inequality`; the boundary is the same as
ours: the signed estimate is an input, not a theorem.  No `sorry`/`axiom` is used
(so it is honest), and no gap closure for our `Cor312EpsilonArithmeticComparison`
follows.  This file abstracts that schema in our own terms; no external import. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GogopexCor312AuditActual

/-! ## 1. The exact Gogopex schema, abstracted -/

inductive PilotSide where
  | theta
  | q
deriving DecidableEq

structure PilotLogVolume where
  side : PilotSide
  value : Real

/-- Gogopex `Corollary312Inequality`: `-theta.value >= -q.value`. -/
def Corollary312Inequality (theta q : PilotLogVolume) : Prop :=
  -theta.value >= -q.value

/-- Gogopex sign conversion: signed value `s` becomes stored value `-s`. -/
def signedPilotLogVolume (side : PilotSide) (signedValue : Real) : PilotLogVolume :=
  { side := side, value := -signedValue }

/-- Gogopex `corollary312_of_signed_le`: only `linarith`; the inequality is an
input hypothesis. -/
theorem corollary312_of_signed_le {thetaSigned qSigned : Real}
    (hle : qSigned <= thetaSigned) :
    Corollary312Inequality (signedPilotLogVolume PilotSide.theta thetaSigned)
      (signedPilotLogVolume PilotSide.q qSigned) := by
  unfold Corollary312Inequality signedPilotLogVolume
  linarith

/-- Gogopex `Corollary312ComparisonData`: the signed comparison is a FIELD. -/
structure Corollary312ComparisonData where
  thetaSigned : Real
  qSigned : Real
  q_positive : 0 < -qSigned
  qSigned_le_thetaSigned : qSigned <= thetaSigned

theorem comparisonData_corollary312 (data : Corollary312ComparisonData) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta data.thetaSigned)
      (signedPilotLogVolume PilotSide.q data.qSigned) :=
  corollary312_of_signed_le data.qSigned_le_thetaSigned

/-! ## 2. The source-obligation LEDGER shape (Gogopex boundary) -/

/-- Abstract shape of the IUT III data that Gogopex stores as `SourceObligationLedger`
fields: certified output / structured certificate / chart / q-value / theta bound /
target volume / membership / normalization.  These are HYPOTHESES here, exactly as
in Gogopex. -/
structure SourceObligationLedgerShape where
  qSigned : Real
  thetaSigned : Real
  targetSigned : Real
  q_le_target : qSigned <= targetSigned
  target_le_theta : targetSigned <= thetaSigned
  q_positive : 0 < -qSigned
  normalization : Prop

/-- The ledger derives the signed inequality (Gogopex `threeTermComparison`). -/
theorem ledger_qSigned_le_thetaSigned (L : SourceObligationLedgerShape) :
    L.qSigned <= L.thetaSigned :=
  le_trans L.q_le_target L.target_le_theta

/-- The ledger therefore yields the schema conclusion. -/
theorem ledger_corollary312 (L : SourceObligationLedgerShape) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta L.thetaSigned)
      (signedPilotLogVolume PilotSide.q L.qSigned) :=
  corollary312_of_signed_le (ledger_qSigned_le_thetaSigned L)

/-! ## 3. Audit verdict rows -/

def gogopexAuditRows : List (String × String × String) :=
  [ ("CorollarySchema exact def", "Corollary312Inequality = -theta.value >= -q.value", "SCHEMA"),
    ("corollary312_of_signed_le", "linarith from hle : qSigned <= thetaSigned", "SCHEMA (assumes inequality)"),
    ("Corollary312ComparisonData", "qSigned_le_thetaSigned field", "ASSUMES signed comparison"),
    ("SourceObligationLedger", "q_le_target + target_le_theta fields", "ASSUMES IUT III data"),
    ("IUTStage1Source 54,738 lines", "ledger plumbing; endpoints rfl/Subsingleton.elim", "SCAFFOLD/AUDIT, not 3.12 proof"),
    ("sorry/axiom count", "0 / 0 in schema+source files", "HONEST but conditional"),
    ("boundary", "SourceObligationLedger -> Corollary312Inequality", "CONDITIONAL; same as ours"),
    ("our Gap1/Gap2", "height_le_normalizedRegionVolume / regionVolume_le_normalizedWeight", "NOT closed by Gogopex") ]

theorem gogopexAuditRows_length : gogopexAuditRows.length = 8 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1GogopexCor312AuditActual.corollary312_of_signed_le
#print axioms LeanFormal.IUT.XiFPaper.Mzk1GogopexCor312AuditActual.ledger_corollary312

end LeanFormal.IUT.XiFPaper.Mzk1GogopexCor312AuditActual

end