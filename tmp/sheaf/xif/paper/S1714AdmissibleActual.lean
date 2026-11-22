import tmp.sheaf.xif.paper.S1712OddResidueActual
import tmp.sheaf.xif.paper.S1711RationalSplitAtFiveBridge

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1711AdmissibleRealizationActual
open LeanFormal.IUT.XiFPaper.S1712OddResidueActual

namespace LeanFormal.IUT.XiFPaper.S1714AdmissibleActual

theorem S1714Split : S1711RationalSplitAtFive :=
  _root_.S1711RationalSplitAtFive

theorem S1714Admissible : S1667Admissible :=
  S1712Admissible_of S1714Split

#print axioms S1714Admissible

end LeanFormal.IUT.XiFPaper.S1714AdmissibleActual
