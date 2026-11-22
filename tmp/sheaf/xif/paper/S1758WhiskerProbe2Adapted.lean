import tmp.sheaf.xif.paper.S1757LiftFunctorialityActual

noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1755TwoYonedaSmallnessActual
open LeanFormal.IUT.XiFPaper.S1757LiftFunctorialityActual
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1758WhiskerProbe2Adapted

variable {A B : S1728Cover}

example {f : S1728CoverMap A B} :
    True := by
  let W : (S1755Square B).TwoPullbackWitness := (S1755BaseChange B).isPullback
  trivial

end LeanFormal.IUT.XiFPaper.S1758WhiskerProbe2Adapted
end
