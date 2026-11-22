import tmp.sheaf.xif.paper.S2893A6QIsStackActual
import tmp.sheaf.xif.paper.S2899A6QPrestackActual
import tmp.sheaf.xif.paper.S2903A6QEffectiveDescentActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2893A6QIsStackActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.InitialThetaSource
namespace LeanFormal.IUT.XiFPaper.S2975A6QIsStackInhabitant

def S2975A6QIsStack : Prop :=
  S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology S2847A6.F)

/-- Conditional actual inhabitant: explicit prestack + effective descent give IsStack. -/
noncomputable def S2975A6QIsStack_of_prestack_descent
    (hP : S2882A6Q.IsPrestack (Iut.SchemeOverField.etaleTopology S2847A6.F))
    (hD : S2893A6QEffectiveDescent) :
    S2975A6QIsStack :=
  (S2893A6QIsStack_iff_descent).mpr ⟨hP, hD⟩

/-- Converse: IsStack gives the descent API. -/
theorem S2975A6QDescentAPI_of_isStack (h : S2975A6QIsStack) :
    S2893A6QDescentAPI :=
  (S2893A6QIsStack_iff_descent).mp h

#check S2975A6QIsStack_of_prestack_descent
#check S2975A6QDescentAPI_of_isStack
#print axioms S2975A6QIsStack_of_prestack_descent

end LeanFormal.IUT.XiFPaper.S2975A6QIsStackInhabitant