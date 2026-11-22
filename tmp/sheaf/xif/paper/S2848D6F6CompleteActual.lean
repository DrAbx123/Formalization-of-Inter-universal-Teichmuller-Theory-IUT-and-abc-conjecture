import tmp.sheaf.xif.paper.S2846D6F6MissingActual
import tmp.sheaf.xif.paper.S2845ZeroPreimageActual
import tmp.sheaf.xif.paper.S2847D6F6NondegenerateActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2845ZeroPreimageActual
open LeanFormal.IUT.XiFPaper.S2846D6F6MissingActual
open LeanFormal.IUT.XiFPaper.S2847D6F6NondegenerateActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2848D6F6CompleteActual

/-- Complete D6 geometric realization on F6: 37a1 base-changed to F6,
nondegenerate etale stack fiber, and actual curve-point realization. -/
noncomputable def S2848D6 : MissingD6GeometricRealization S2844D6F6BaseChangeActual.K :=
  S2846D6 S2845ZeroPreimage S2847_not_isPointFiber

#check S2848D6
#print axioms S2848D6

end LeanFormal.IUT.XiFPaper.S2848D6F6CompleteActual
end
