import tmp.sheaf.xif.paper.S2975A6QIsStackInhabitant
import tmp.sheaf.xif.paper.S2899A6QPrestackActual
import tmp.sheaf.xif.paper.S2903A6QEffectiveDescentActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2893A6QIsStackActual
open LeanFormal.IUT.XiFPaper.S2899A6QPrestackActual
open LeanFormal.IUT.XiFPaper.S2903A6QEffectiveDescentActual
open LeanFormal.IUT.XiFPaper.S2975A6QIsStackInhabitant
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2977A6QIsStackActual

/-- A6Q IsStack from the A1 prestack and A2 effective descent. -/
noncomputable def S2977A6QIsStack
    (hP : S2899A6QIsPrestack)
    (hD : S2903A6QEffectiveDescent) :
    S2975A6QIsStack :=
  S2975A6QIsStack_of_prestack_descent hP hD

/-- Converse: A6Q IsStack supplies the A2 descent API. -/
theorem S2977A6QDescentAPI_of_isStack
    (h : S2975A6QIsStack) : S2893A6QDescentAPI :=
  S2975A6QDescentAPI_of_isStack h

/-- Exact missing object: actual inhabitants of the A1 prestack and A2 effective
descent properties. -/
structure S2977MissingInputs : Prop where
  prestack : S2899A6QIsPrestack
  descent : S2903A6QEffectiveDescent

/-- From the missing inputs, A6Q IsStack follows. -/
noncomputable def S2977A6QIsStack_of_missing
    (M : S2977MissingInputs) : S2975A6QIsStack :=
  S2977A6QIsStack M.prestack M.descent

#check S2977A6QIsStack
#check S2977A6QDescentAPI_of_isStack
#check S2977MissingInputs
#check S2977A6QIsStack_of_missing
#print axioms S2977A6QIsStack

end LeanFormal.IUT.XiFPaper.S2977A6QIsStackActual
end
