import tmp.sheaf.xif.paper.S3133ModelRouteM1StatusActual
import tmp.sheaf.xif.paper.S3133ModelRouteM2bStatusActual
import tmp.sheaf.xif.paper.S3135TreeModelBaseUnitScalingActual

/-!
# Model-route in-model R1 status (component, not a paper object)

COMPONENT, not a paper object.  Named consumers: mainline/lattice in-model R1
record, shehdd 3rd-reopen checklist.

Combined in-model R1 status on the EXISTING concrete model chain:
* M1: explicit placeToMod datum with injective map constructed in-model
  (S3133ModelRouteM1Status);
* M2b: qVFamily := model q, descent definitional (S3133ModelRouteM2bStatus);
* nontrivial procession scaling witness: abc's actual baseUnit = -1 in Q_5^
  (S3135TreeModelBaseUnitScalingActual), filling the qpilot interface
  S3133TreeModelBaseUnitScaling.
M0/M3 and F4.a/F4.b are elsewhere (Gaussian model components; abc construction).
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133ModelRouteR1StatusActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3133ExistingModelAdaptationActual
open LeanFormal.IUT.XiFPaper.S3133ModelRouteM1StatusActual
open LeanFormal.IUT.XiFPaper.S3133ModelRouteM2bStatusActual
open LeanFormal.IUT.XiFPaper.S3135TreeModelBaseUnitScalingActual

/-- Combined in-model R1 status. -/
def S3133ModelRouteR1Status : Prop :=
  S3133ModelRouteM1Status ∧ S3133ModelRouteM2bStatus ∧
    Nonempty S3133TreeModelBaseUnitScaling

/-- The combined in-model R1 status holds: M1 constructed, M2b definitional,
and the nontrivial baseUnit witness supplied. -/
theorem S3133ModelRouteR1Status_holds : S3133ModelRouteR1Status :=
  ⟨S3133ModelRouteM1Status_holds, S3133ModelRouteM2bStatus_holds,
    ⟨s3135_treeModelBaseUnitScaling⟩⟩

end LeanFormal.IUT.XiFPaper.S3133ModelRouteR1StatusActual
