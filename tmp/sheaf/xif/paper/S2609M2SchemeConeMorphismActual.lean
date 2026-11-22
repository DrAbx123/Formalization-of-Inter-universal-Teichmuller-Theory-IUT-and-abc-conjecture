import tmp.sheaf.xif.paper.S2608M2QConeMorphismActual
import tmp.sheaf.xif.paper.S2607M2SchemeConeMorphismPartial

/-! # S2609: full schemeConeMorphism -/

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2601M2WitnessGoal
open LeanFormal.IUT.XiFPaper.S2602M2SchemeWitnessGoal
open LeanFormal.IUT.XiFPaper.S2604M2BaseWitnessPartial
open LeanFormal.IUT.XiFPaper.S2607M2SchemeConeMorphismPartial
open LeanFormal.IUT.XiFPaper.S2608M2QConeMorphismActual

namespace LeanFormal.IUT.XiFPaper.S2609M2SchemeConeMorphismActual

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)

noncomputable def schemeConeMorphism
    {W : EtaleStackPseudofunctor S1726K}
    {source target : (@baseSquare X Y m A T s vy Q).Cone W}
    (f : (@baseSquare X Y m A T s vy Q).ConeMorphism source target) :
    (@schemeSquare X Y m A T s vy Q).ConeMorphism
      (@schemeCone X Y m A T s vy Q W source)
      (@schemeCone X Y m A T s vy Q W target) :=
  @schemeConeMorphismOf X Y m A T s vy Q W source target f
    (Q.isPullback.liftTwoCell W
      (@coneQ X Y m A T s vy Q W source)
      (@coneQ X Y m A T s vy Q W target)
      (@qConeMorphism X Y m A T s vy Q W source target f))

#check schemeConeMorphism
#print axioms schemeConeMorphism

end LeanFormal.IUT.XiFPaper.S2609M2SchemeConeMorphismActual
end
