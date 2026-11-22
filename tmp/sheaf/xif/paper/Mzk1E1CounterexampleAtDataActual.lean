/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.PaperQPilotObject
import tmp.sheaf.xif.paper.Mzk1E1OrderActual
import Mathlib.Tactic

/-! # A951 hull: bare E1 counterexample at SourceDefinition31Data level

For any `S : SourceDefinition31Data` with nonempty bad places,
`sourceQPilotSignedLog S = -sourceBadQAbsLog S < 0`, hence
`QSideContribution (sourceQPilotSignedLog S) ≠ 0` and the bare
`E1PaperScaledHullForm` fails.  This is not tied to a concrete I/place. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1E1CounterexampleAtDataActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.Mzk1E1OrderActual

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)

/-- Negativity at the Definition 3.1 data level (re-export). -/
theorem sourceQPilotSignedLog_neg (hbad : Nonempty S.badPlaces) :
    sourceQPilotSignedLog S < 0 :=
  sourceQPilotSignedLog_neg_of_nonempty S hbad

/-- The q-side contribution is nonzero. -/
theorem qSideContribution_source_ne_zero (hbad : Nonempty S.badPlaces) :
    QSideContribution (sourceQPilotSignedLog S) ≠ 0 := by
  unfold QSideContribution
  exact neg_ne_zero.mpr (ne_of_lt (sourceQPilotSignedLog_neg S hbad))

/-- The bare E1 paper equality FAILS at the data level. -/
theorem bareE1_false_at_data (hbad : Nonempty S.badPlaces) :
    ¬ E1PaperScaledHullForm (QSideContribution (sourceQPilotSignedLog S)) := by
  rw [e1_iff_qside_zero]
  exact qSideContribution_source_ne_zero S hbad

def rows : List (String × String × String) :=
  [ ("sourceQPilotSignedLog<0", "Nonempty badPlaces => signed log < 0", "PROVED"),
    ("qSide!=0", "QSideContribution(sourceQPilotSignedLog S) != 0", "PROVED"),
    ("bare E1 false", "not E1PaperScaledHullForm ...", "PROVED"),
    ("scope", "any SourceDefinition31Data with nonempty badPlaces", "THEOREM") ]

theorem rows_length : rows.length = 4 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1E1CounterexampleAtDataActual.sourceQPilotSignedLog_neg
#print axioms LeanFormal.IUT.XiFPaper.Mzk1E1CounterexampleAtDataActual.qSideContribution_source_ne_zero
#print axioms LeanFormal.IUT.XiFPaper.Mzk1E1CounterexampleAtDataActual.bareE1_false_at_data

end LeanFormal.IUT.XiFPaper.Mzk1E1CounterexampleAtDataActual

end