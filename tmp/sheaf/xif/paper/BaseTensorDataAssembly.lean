import tmp.sheaf.xif.paper.BaseTensorInsertionActual
import tmp.sheaf.xif.paper.BaseQDescentAssembly
import tmp.sheaf.xif.paper.C3DonorUnconditionalActual

/-! # Full BaseTensorData conditional assembly

Task-690 integration.  The actual Fmod BaseTensorData is constructed in
`BaseTensorInsertionActual` from an actual `BaseQDescentData`.  The actual
`BaseQDescentData` is assembled in `BaseQDescentAssembly` from the relative
norm descent and the exact missing contraction law `LocalNormValuationGap`.

This file composes them:

* from the exact gap, build `BaseQDescentData`, then the full
  `BaseTensorData`;
* expose the conditional nonemptiness and the q/tensor-lading laws;
* `#check` the actual consumers `sourcePilotRegionDonorsOfBaseQ`,
  `BaseTensorData`, and the assembled objects.

The only missing object is the actual `LocalNormValuationGap`
(equivalently `NativeQRelativeNormContraction`); no arbitrary descent, q,
unit, tensor, axiom, or sorry is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.BaseTensorDataAssembly

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.XiFPaper.BasePlaceQCandidateActual
open LeanFormal.IUT.XiFPaper.BaseQDescentAssembly
open LeanFormal.IUT.XiFPaper.BaseTensorInsertionActual
open LeanFormal.IUT.N8Closure.C3DonorUnconditionalActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Full BaseQDescentData from the exact missing contraction gap. -/
noncomputable def fullBaseQDescentData
    (h : LocalNormValuationGap (X := X)) : BaseQDescentData (X := X) :=
  baseQDescentDataOfGap (X := X) h

/-- The base q candidate assembled from the gap. -/
noncomputable def fullBaseQCandidate
    (h : LocalNormValuationGap (X := X)) :
    FinitePlaceQCandidate (nativeC3Place X).val :=
  baseQCandidateOfDescent (X := X) (fullBaseQDescentData X h)

/-- Full Fmod-indexed BaseTensorData assembled from the gap. -/
noncomputable def fullBaseTensorData
    (h : LocalNormValuationGap (X := X)) :
    BaseTensorData (X := X)
      (baseQCandidateOfDescent (X := X) (fullBaseQDescentData X h)) :=
  baseTensorDataActual X (fullBaseQDescentData X h)

@[simp] theorem fullBaseTensorData_tensorLanding
    (h : LocalNormValuationGap (X := X)) :
    (fullBaseTensorData X h).tensorLanding = baseTensorInsertion X := rfl

theorem fullBaseTensorData_tensorLanding_q
    (h : LocalNormValuationGap (X := X)) :
    (fullBaseTensorData X h).tensorLanding
        (baseQCandidateOfDescent (X := X) (fullBaseQDescentData X h)).q =
      ((fullBaseTensorData X h).tensorUnit : baseTensorBlock (X := X)) :=
  rfl

theorem fullBaseTensorData_tensorUnit_ne_zero
    (h : LocalNormValuationGap (X := X)) :
    ((fullBaseTensorData X h).tensorUnit : baseTensorBlock (X := X)) ≠ 0 :=
  Units.ne_zero (fullBaseTensorData X h).tensorUnit

theorem fullBaseTensorData_nonempty_of_gap
    (h : LocalNormValuationGap (X := X)) :
    Nonempty (BaseTensorData (X := X)
      (baseQCandidateOfDescent (X := X) (fullBaseQDescentData X h))) :=
  ⟨fullBaseTensorData X h⟩

/-- Exact missing primitive: the actual local norm valuation/contraction gap. -/
def FullBaseTensorDataGap : Prop :=
  LocalNormValuationGap (X := X)

theorem fullBaseTensorData_of_gap
    (h : FullBaseTensorDataGap (X := X)) :
    Nonempty (BaseTensorData (X := X)
      (baseQCandidateOfDescent (X := X) (fullBaseQDescentData X h))) :=
  fullBaseTensorData_nonempty_of_gap X h

/-- Consumer check: the assembled tensor data feeds the conditional C3 donor. -/
#check sourcePilotRegionDonorsOfBaseQ
#check BaseTensorData
#check baseTensorDataActual
#check fullBaseTensorData
#check fullBaseTensorData_nonempty_of_gap
#check BaseQDescentData
#check LocalNormValuationGap

end LeanFormal.IUT.XiFPaper.BaseTensorDataAssembly

end
