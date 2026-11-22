/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7/#6: StepXIContract evidence interface draft (GAP; fields are Props) -/

/-
| field | value |
|---|---|
| Status | DRAFT INTERFACE: proposed evidence fields for the three WallObligations; no field is proved |
| GAP | GAP-P7-CONTRACT: no StepXIContract field/linkage in tree; this structure is a target schema, not evidence |
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIEvidenceInterfaceActual

/-- Proposed evidence payload for the three contract obligations.  This is a
schema only: inhabiting it requires the actual obligations (GAP-P7-CONTRACT). -/
structure StepXIEvidenceInterface where
  holomorphicHullEvidence : Prop
  determinantNormalizationEvidence : Prop
  logVolumeComparisonEvidence : Prop

/-- A consumer only takes the schema as an explicit datum. -/
def stepXIEvidenceInterface_id
    (E : StepXIEvidenceInterface) :
    StepXIEvidenceInterface := E

end LeanFormal.IUT.XiFPaper.Mzk1StepXIEvidenceInterfaceActual