import tmp.sheaf.xif.paper.S1714AdmissibleActual
import tmp.sheaf.xif.paper.S1715SourceTorsionClauseActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1714AdmissibleActual

namespace LeanFormal.IUT.XiFPaper.S1716D5Summary

/-- Verified D5 entry point: the paper condition (b) admissible curve is
unconditional. -/
theorem S1716D5Admissible : S1667Admissible :=
  S1714Admissible

/-- The split-reduction component, in its exact source-clause Prop. -/
theorem S1716D5SplitAtFive :
    LeanFormal.IUT.XiFPaper.S1711AdmissibleRealizationActual.S1711RationalSplitAtFive :=
  _root_.S1711RationalSplitAtFive

#print axioms S1716D5Admissible
#print axioms S1716D5SplitAtFive

end LeanFormal.IUT.XiFPaper.S1716D5Summary
