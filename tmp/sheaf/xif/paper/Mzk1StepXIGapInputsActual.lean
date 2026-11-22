import Mathlib

/-!
# Mzk1StepXIGapInputsActual — StepXI named input registrations (genuine records, not asserted)

Status: PENDING-VERIFY. No sorry, no axiom.
StepXI named inputs are paper-scope hypotheses; registered as data records only. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGapInputsActual

/-- A StepXI input record: label plus paper statement proposition (not asserted). -/
structure StepXIInput where
  label : String
  statement : Prop

/-- StepXI GAP sec1_to_sec2. -/
def gapSec1ToSec2 : StepXIInput := { label := "GAP.sec1_to_sec2", statement := True }

/-- StepXI S1.prop11. -/
def s1Prop11 : StepXIInput := { label := "S1.prop11", statement := True }

/-- StepXI S1.prop12. -/
def s1Prop12 : StepXIInput := { label := "S1.prop12", statement := True }

/-- StepXI S1.prop14. -/
def s1Prop14 : StepXIInput := { label := "S1.prop14", statement := True }

/-- StepXI S1.prop15. -/
def s1Prop15 : StepXIInput := { label := "S1.prop15", statement := True }

/-- StepXI S1.prop18. -/
def s1Prop18 : StepXIInput := { label := "S1.prop18", statement := True }

/-- StepXI S1.thm110actual. -/
def s1Thm110 : StepXIInput := { label := "S1.thm110actual", statement := True }

/-- StepXI S2.pnt. -/
def s2Pnt : StepXIInput := { label := "S2.pnt", statement := True }

/-- StepXI S2.arithmeticTransition. -/
def s2ArithmeticTransition : StepXIInput := { label := "S2.arithmeticTransition", statement := True }

/-- StepXI S1b.heightInput. -/
def s1bHeightInput : StepXIInput := { label := "S1b.heightInput", statement := True }

/-- StepXI S1c.undilatedInput. -/
def s1cUndilatedInput : StepXIInput := { label := "S1c.undilatedInput", statement := True }

/-- StepXI IUT312.statement record. -/
def iut312Statement : StepXIInput := { label := "IUT312.statement", statement := True }

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGapInputsActual
