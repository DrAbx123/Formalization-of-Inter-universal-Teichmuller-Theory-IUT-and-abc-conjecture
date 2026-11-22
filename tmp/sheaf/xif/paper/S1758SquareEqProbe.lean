import tmp.sheaf.xif.paper.S1757LiftFunctorialityActual

noncomputable section
set_option maxHeartbeats 20000000
namespace LeanFormal.IUT.XiFPaper.S1758SquareEqProbe

open LeanFormal.IUT.XiFPaper.S1757LiftFunctorialityActual
open LeanFormal.IUT.XiFPaper.S1755TwoYonedaSmallnessActual
open LeanFormal.IUT.XiFPaper.S1755ConcreteIntegralClosureCActual

example (B : S1728Cover) :
    S1755Square B =
      EtalePseudofunctorSquare.mk
        (S1755BaseChange B).toSource
        (S1755BaseChange B).projectionMap.transformation
        B.map S1733BasePoint
        (S1755BaseChange B).commutes := rfl

end LeanFormal.IUT.XiFPaper.S1758SquareEqProbe
