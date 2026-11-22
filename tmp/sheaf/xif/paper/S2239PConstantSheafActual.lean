import tmp.sheaf.xif.paper.S2234PConstantCorrectActual
import Mathlib.CategoryTheory.Sites.LeftExact

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2234PConstantCorrectActual
open LeanFormal.IUT.XiFPaper.S2192QHomSheavesActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2239PConstantSheafActual

variable (S : Iut.SchemeOverField S1726K)

/-- The Type-valued sheafification API needed for the constant sheaf P. -/
def S2239HasWeakSheafify : Prop :=
  Nonempty (HasWeakSheafify ((Iut.SchemeOverField.etaleTopology S1726K).over S) Type)

/-- Exact first missing for the Type-valued constant sheaf P. -/
def S2239ConstantSheafFirstMissing : Prop :=
  S2239HasWeakSheafify S

/-- The alternative finite-coproduct of terminal sheaf route. -/
def S2239FiniteCoproductFirstMissing : Prop :=
  Nonempty (Sheaf ((Iut.SchemeOverField.etaleTopology S1726K).over S) (Type))

end LeanFormal.IUT.XiFPaper.S2239PConstantSheafActual

end
