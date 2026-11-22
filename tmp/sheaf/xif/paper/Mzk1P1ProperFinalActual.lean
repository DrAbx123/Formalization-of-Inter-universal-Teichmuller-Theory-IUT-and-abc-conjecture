/- G-A final assembly: P^1_glued is proper over Spec Q.
Separated comes from david's valuative uniqueness; universally closed was established
from the existence part; locally of finite type is the instance from Mzk1P1ProperActual. -/
import tmp.sheaf.xif.paper.Mzk1P1ValuativeUniquenessActual
import tmp.sheaf.xif.paper.Mzk1P1UniversallyClosedActual
noncomputable section
open AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper.Mzk1P1ProperFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1P1ProperActual

/-- **P^1_glued is separated over Spec Q** (uniqueness part of the valuative criterion). -/
theorem p1GluedToBase_isSeparated : IsSeparated p1GluedToBase :=
  IsSeparated.of_valuativeCriterion
    (f := p1GluedToBase)
    LeanFormal.IUT.XiFPaper.Mzk1P1ValuativeUniquenessActual.valuativeCriterion_uniqueness

/-- **P^1_glued is proper over Spec Q** (the geometric input for IsProper(Y_n)). -/
theorem p1GluedToBase_isProper : IsProper p1GluedToBase :=
  IsProper.of_valuativeCriterion (f := p1GluedToBase)
    LeanFormal.IUT.XiFPaper.Mzk1P1ValuativeUniquenessActual.p1GluedToBase_valuativeCriterion

#print axioms p1GluedToBase_isSeparated
#print axioms p1GluedToBase_isProper
end LeanFormal.IUT.XiFPaper.Mzk1P1ProperFinalActual
