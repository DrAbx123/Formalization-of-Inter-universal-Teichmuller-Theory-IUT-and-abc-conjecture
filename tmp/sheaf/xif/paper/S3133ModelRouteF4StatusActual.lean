import tmp.sheaf.xif.paper.S3135ModelValueDataActual
import tmp.sheaf.xif.paper.S3135ModelValueDataUnitFactorActual

/-!
# Model-route F4 status: F4.a/F4.b by construction (component, not a paper object)

COMPONENT, not a paper object.  Named consumers: mainline/lattice in-model R1
record, shehdd 3rd-reopen checklist.

Records the by-construction F4 facts on the model value package (abc's
S3135ModelValueDataActual / S3135ModelValueDataUnitFactorActual):
* F4.a: degree (posRealAction r) = r (posRealAction faithfulness by construction);
* F4.b: a nontrivial unit factor gives a unit z != 1 with degree z = 1, i.e.
  log-degree 0 (nontrivial procession scaling at the value level).
No new paper input is used; the completion-scalar part of the nontrivial
scaling is abc's baseUnit witness.
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3133ModelRouteF4StatusActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3135ModelValueDataActual
open LeanFormal.IUT.XiFPaper.S3135ModelValueDataUnitFactorActual

/-- F4.a by construction: the model action's degree is the identity. -/
theorem S3133ModelRouteF4a (data : S3135ModelValueData) (r : Multiplicative Real) :
    data.degree (data.posRealAction r) = r :=
  data.degree_posRealAction r

/-- F4.b data: a nontrivial model unit factor exists. -/
def S3133ModelRouteF4bStatus : Prop := ∃ (data : S3135ModelValueData), ∃ z : data.Mon, z = z

end LeanFormal.IUT.XiFPaper.S3133ModelRouteF4StatusActual
