/- G-A: P^1_glued is universally closed over Spec Q (the existence part of the valuative
criterion, together with quasi-compactness).  This is a genuine component of IsProper
(isProper = IsSeparated ∧ UniversallyClosed ∧ LocallyOfFiniteType).  The separation part
waits for david's uniqueness file. -/
import tmp.sheaf.xif.paper.Mzk1P1ValuativeActual
noncomputable section
open AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper.Mzk1P1UniversallyClosedActual

/-- **P^1_glued is universally closed over Spec Q.** -/
theorem p1GluedToBase_universallyClosed :
    UniversallyClosed (LeanFormal.IUT.XiFPaper.Mzk1P1ProperActual.p1GluedToBase) :=
  UniversallyClosed.of_valuativeCriterion
    (f := LeanFormal.IUT.XiFPaper.Mzk1P1ProperActual.p1GluedToBase)
    LeanFormal.IUT.XiFPaper.Mzk1P1ValuativeActual.valuativeCriterion_existence

#print axioms p1GluedToBase_universallyClosed
end LeanFormal.IUT.XiFPaper.Mzk1P1UniversallyClosedActual
