import tmp.sheaf.xif.paper.S2540CorrectedObjectMapActual
import tmp.sheaf.xif.paper.S2539FaithfulActual
import tmp.sheaf.xif.paper.S2540FullGoalActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2538AffineCoverEquivActual
open LeanFormal.IUT.XiFPaper.S2519InvFunctorActual
open LeanFormal.IUT.XiFPaper.S2539FaithfulActual
open LeanFormal.IUT.XiFPaper.S2540CorrectedObjectMapActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2542FunctorFaithfulActual

instance S2542InvFunctorFaithful : S2519InvFunctor.Faithful where
  map_injective := by
    intro C D f g h
    exact S2539Faithful h

theorem S2542Functor_faithful : S2540Functor.Faithful where
  map_injective := by
    intro A B f g h
    dsimp [S2540Functor] at h
    have h' := S2539Faithful h
    exact (S2538AffineCoverEquiv.inverse).map_injective h'

#check S2542Functor_faithful
#print axioms S2542Functor_faithful
end LeanFormal.IUT.XiFPaper.S2542FunctorFaithfulActual
end