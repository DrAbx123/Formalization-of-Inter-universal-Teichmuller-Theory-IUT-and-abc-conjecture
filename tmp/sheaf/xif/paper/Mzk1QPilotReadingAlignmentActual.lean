/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.QPilotObjectActual
import tmp.sheaf.xif.paper.Mzk1QSideExplicitActual
import Mathlib.Tactic

/-! # A824 hull: `PaperQPilotObjectActual` donors and q-reading `-A`

`PaperQPilotObjectActual` has fields `line : QPilotLineActual` (C1, C2, C3),
`strip`, `oneColumn`, `logKummer`, `oneZero` and two equalities.  The C1/C2,
strip/one-column/one-zero data are external source obligations (no green
constructors), so a genuine inhabitant is built only from explicit donors.

q-reading alignment: `qPilotLogVolumeReading P = -|log q| = log ||q||`
(QSide).  Define `APaper P = -qPilotLogVolumeReading P` (the positive paper
magnitude `|log q|`); then `qPilotLogVolumeReading P = -APaper P`.  The paper
normalized `A = log q/(2ℓ)` is `APaper/(2ℓ)`, giving
`qReading = -(2ℓ)·(APaper/(2ℓ))`; the choice of the `2ℓ` normalization is the
documented convention (QSide/lana), not a new equality. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1QPilotReadingAlignmentActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.XiFPaper.QPilotObjectActual
open LeanFormal.IUT.XiFPaper.Mzk1QSideExplicitActual

universe ua uv upi umon ui uC3 uD3

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- Exact donor data for a genuine `PaperQPilotObjectActual` inhabitant. -/
structure PaperQPilotObjectDonors
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  C1 : SourceInputBinding I
  C2 : SourceLogKummerData I C1
  C3 : SourcePilotRegionData.{ua, uv, upi, umon, ui, uC3, uD3} (l := l) (V := V) I
  strip : SourceFTimesMuPrimeStrip.{uv, uM, uP} V
  oneColumn : SourceOneColumnArithmeticHolomorphicStructure V
  oneZero : OneZeroPoint

/-- Constructor from donors. -/
noncomputable def paperQPilotObjectOfDonors
    (D : PaperQPilotObjectDonors (l := l) (V := V) I) :
    PaperQPilotObjectActual (l := l) (I := I) where
  line := { C1 := D.C1, C2 := D.C2, C3 := D.C3 }
  strip := D.strip
  oneColumn := D.oneColumn
  logKummer := D.C2
  logKummer_eq := rfl
  oneZero := D.oneZero
  oneZero_eq := rfl

theorem paperQPilotObject_nonempty_of_donors
    (D : PaperQPilotObjectDonors (l := l) (V := V) I) :
    Nonempty (PaperQPilotObjectActual (l := l) (I := I)) :=
  ⟨paperQPilotObjectOfDonors D⟩

variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- Positive paper q magnitude `A = -qReading = |log q|`. -/
noncomputable def APaper : ℝ := -qPilotLogVolumeReading P

theorem APaper_eq : APaper P = -qPilotLogVolumeReading P := rfl

theorem APaper_nonneg : 0 ≤ APaper P := by
  unfold APaper
  linarith [qPilotLogVolumeReading_nonpos P]

/-- **q-reading alignment**: `qPilotLogVolumeReading P = -APaper P`. -/
theorem qPilotLogVolumeReading_eq_neg_APaper :
    qPilotLogVolumeReading P = -APaper P := by
  unfold APaper
  ring

/-- Paper-normalized magnitude `A = log q/(2ℓ)` (as APaper/(2ℓ)). -/
noncomputable def APaperNormalized (l : PrimeGeFive) : ℝ := APaper P / (2 * (l.value : ℝ))

theorem qReading_eq_neg_twoL_mul_APaperNormalized (l : PrimeGeFive) :
    qPilotLogVolumeReading P = -(2 * (l.value : ℝ)) * APaperNormalized P l := by
  unfold APaperNormalized APaper
  field_simp

theorem APaperNormalized_eq_logQ_div_twoL (h : APaper P = Real.log ‖P.line.C3.q.q‖) (l : PrimeGeFive) :
    APaperNormalized P l = Real.log ‖P.line.C3.q.q‖ / (2 * (l.value : ℝ)) := by
  unfold APaperNormalized
  rw [h]

def alignmentRows : List (String × String × String) :=
  [ ("inhabitant", "PaperQPilotObjectActual from explicit C1/C2/C3/strip/oneColumn/oneZero donors", "CONDITIONAL (paperQPilotObjectOfDonors); external source data not constructed"),
    ("missing donors", "SourceInputBinding, SourceLogKummerData, SourceFTimesMuPrimeStrip, oneColumn, OneZeroPoint", "GAP (no green constructors)"),
    ("q reading", "qPilotLogVolumeReading P = -|log q| = log||q||", "GREEN (QSide)"),
    ("A definition", "APaper = -qReading = |log q|", "DEF"),
    ("-A alignment", "qReading = -APaper", "PROVED (qPilotLogVolumeReading_eq_neg_APaper)"),
    ("2l normalization", "qReading = -(2l)*(APaper/(2l))", "PROVED (qReading_eq_neg_twoL_mul_APaperNormalized)"),
    ("paper A convention", "A_paper = log q/(2l) = APaper/(2l) if APaper=log||q||", "PROVED (APaperNormalized_eq_logQ_div_twoL; needs APaper=log norm)") ]

theorem alignmentRows_length : alignmentRows.length = 7 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1QPilotReadingAlignmentActual.paperQPilotObject_nonempty_of_donors
#print axioms LeanFormal.IUT.XiFPaper.Mzk1QPilotReadingAlignmentActual.qPilotLogVolumeReading_eq_neg_APaper
#print axioms LeanFormal.IUT.XiFPaper.Mzk1QPilotReadingAlignmentActual.qReading_eq_neg_twoL_mul_APaperNormalized

end LeanFormal.IUT.XiFPaper.Mzk1QPilotReadingAlignmentActual

end