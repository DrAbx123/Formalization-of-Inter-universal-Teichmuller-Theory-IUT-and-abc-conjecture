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

namespace LeanFormal.IUT.XiFPaper.S1758SquareEqActual

variable {B : S1728Cover}

/-- The S1755 square is definitionally the literal square used by its
base-change presentation. -/
theorem S1758Square_eq :
    S1755Square B =
      EtalePseudofunctorSquare.mk (S1755BaseChange B).toSource
        (S1755BaseChange B).projectionMap.transformation B.map S1733BasePoint
        (S1755BaseChange B).commutes := rfl

#print axioms S1758Square_eq

end LeanFormal.IUT.XiFPaper.S1758SquareEqActual
end
