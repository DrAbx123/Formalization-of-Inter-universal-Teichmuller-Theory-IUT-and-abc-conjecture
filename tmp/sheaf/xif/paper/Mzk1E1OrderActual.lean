/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A936: E1 order verdict (actual q-pilot order vs E1) -/

/- GREEN FACT (from stepxi's inventory): `OrigXiFPaperQPilotFromSourceLActual.lean:247`
`OrigXiFPaperQPilotOfBoundary` is the actual L paper q-pilot object for the source input
`I` and boundary `b` (`OrigXiFQPilotFirstFieldType`, inhabited by
`OrigXiFQPilotFirstFieldType_nonempty` with `SourceProcessionBoundary.Input.concreteInput l`).
Its q-pilot log-volume field is `sourceQPilotSignedLog I.initial` (rfl, :293-296).

DECISION POINT: E1 (`Mzk1E1DictionaryActual`) asks for the identification
`V_norm = V_hull`; its paper form is `E1PaperScaledHull` and it is equivalent to the
statement that the q-side contribution to the scaled hull vanishes (A910 allocation
discussion).  The q-side contribution is the signed log of the actual source q
(`sourceQPilotSignedLog I.initial`); a CONCRETE numerical order value requires a concrete
`I` (and its source q candidate), which is not available in this file.

VERDICT (see coord/E1-ORDER-VERDICT.md):
- the actual order value is NOT computed here (needs concrete `I`);
- E1 is NOT established for the actual `D`: the q-side contribution is not proved zero;
- the correct identification form (interface) is to ABSORB the q-side into the volume:
  `E1PaperScaledHullForm` holds iff the q-side contribution vanishes; otherwise the
  identification should be stated relative to the q-pilot point (allocation form),
  not as a bare `V_norm = V_hull`.

No sorry/axiom. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1E1OrderActual

/-- Paper E1 form: the q-side contribution to the scaled hull is zero. -/
def E1PaperScaledHullForm (qSideContribution : ℝ) : Prop := qSideContribution = 0

theorem e1_iff_qside_zero (qSideContribution : ℝ) :
    E1PaperScaledHullForm qSideContribution ↔ qSideContribution = 0 := Iff.rfl

/-- The q-side contribution is `-(|log q|)`-shaped (signed log of the actual source q);
whether it is zero is the E1 question. -/
def QSideContribution (signedLogQ : ℝ) : ℝ := -signedLogQ

/-- Allocation form of E1: absorb the q-side into the volume comparison. -/
def E1AllocationForm (V_norm V_hull qSideContribution : ℝ) : Prop :=
  V_norm = V_hull + qSideContribution

theorem e1_allocation_of_zero (V_norm V_hull qSideContribution : ℝ)
    (h : qSideContribution = 0) : E1AllocationForm V_norm V_hull qSideContribution ↔ V_norm = V_hull := by
  unfold E1AllocationForm
  rw [h]
  constructor <;> intro hh <;> linarith

def e1OrderRows : List (String × String × String) :=
  [ ("L paper q-pilot object", "OrigXiFPaperQPilotFromSourceLActual:247 (green)", "GREEN") ,
    ("q-pilot log-volume field", "sourceQPilotSignedLog I.initial (:293)", "GREEN (rfl)") ,
    ("actual q order value", "needs concrete I / source q candidate", "NOT COMPUTED") ,
    ("E1 paper form", "E1PaperScaledHull <-> qSideContribution = 0", "DEF + PROVED iff") ,
    ("E1 for actual D", "qSide zero not proved", "NOT ESTABLISHED") ,
    ("correct identification form", "allocation: V_norm = V_hull + qSide", "INTERFACE (E1AllocationForm)") ]

theorem e1OrderRows_length : e1OrderRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1E1OrderActual
