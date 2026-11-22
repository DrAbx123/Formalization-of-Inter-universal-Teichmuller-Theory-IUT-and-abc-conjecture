import tmp.sheaf.xif.paper.S2542FunctorFaithfulActual
import tmp.sheaf.xif.paper.S2540FullBridgeActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2519InvFunctorActual
open LeanFormal.IUT.XiFPaper.S2540CorrectedObjectMapActual
open LeanFormal.IUT.XiFPaper.S2540FullGoalActual
open LeanFormal.IUT.XiFPaper.S2540FullBridgeActual
open LeanFormal.IUT.XiFPaper.S2538AffineCoverEquivActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2542FunctorFullActual

/-- Conditional Full of the inverse functor from S2540FullLift. -/
theorem S2542InvFunctor_full_of_lift (h : S2540FullLift) :
    S2519InvFunctor.Full :=
  { map_surjective := S2540Full_of_lift h }

/-- Conditional Full of the corrected algebra-side functor. -/
theorem S2542Functor_full_of_lift (h : S2540FullLift) :
    S2540Functor.Full := by
  letI : S2519InvFunctor.Full := S2542InvFunctor_full_of_lift h
  dsimp [S2540Functor]
  infer_instance

#check S2542InvFunctor_full_of_lift
#check S2542Functor_full_of_lift

end LeanFormal.IUT.XiFPaper.S2542FunctorFullActual
end
