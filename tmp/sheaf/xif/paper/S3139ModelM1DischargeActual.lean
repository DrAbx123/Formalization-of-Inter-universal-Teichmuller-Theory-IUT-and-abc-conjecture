import tmp.sheaf.xif.paper.S3133ExistingModelAdaptationActual
import tmp.sheaf.xif.paper.S3133ModelM1PlaceToModActual
import tmp.sheaf.xif.paper.S3139FirstTriangleRouteCompositionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: Option-B in-model M1 discharge (reuse; no re-proof)

The first-triangle route residual (S3139FirstTriangleRouteCompositionActual) keeps
M1 as its placeSelection slot.  Option-B evidence discharges that slot IN-MODEL:
qpilot's S3133ExistingModelAdaptationActual.S3133TreeModelM1Datum and
S3133ModelM1PlaceToModActual.modelPlaceToModDatum are explicit place-to-moduli
data with injective place maps, already proven in those files.  This file records
the discharge and fills the route residual's slot with the in-model evidence.

HONESTY: this discharges M1 only for the EXISTING concrete model (V = Unit /
model V-basis).  It does not discharge general FT.M1 for an arbitrary frozen
input; that remains OPEN, together with M0, the capsule-label link, the stage4
unit map, and the fourth-triangle arithmetic inputs.

**Component, not paper object.**  Registry frozen 13129; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139ModelM1DischargeActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3133ExistingModelAdaptationActual
open LeanFormal.IUT.XiFPaper.S3133ModelM1PlaceToModActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleRouteCompositionActual

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- Option-B in-model M1 evidence: the tree-model place-to-moduli datum and the
V-basis model datum both exist (reuse of qpilot's constructible data). -/
def sourceModelM1Evidence : Prop :=
  Nonempty S3133TreeModelPlaceToModDatum ∧ Nonempty S3133ModelPlaceToModDatum

/-- Option-B in-model M1 is CONSTRUCTIBLE (reused data, no new proof of the model). -/
theorem sourceModelM1Evidence_holds : sourceModelM1Evidence :=
  ⟨⟨S3133TreeModelM1Datum⟩, ⟨modelPlaceToModDatum⟩⟩

/-- The tree-model datum has an injective place map (reuse). -/
theorem sourceModelM1_treeModel_constructible :
    ∃ D : S3133TreeModelPlaceToModDatum, Function.Injective D.placeOf :=
  S3133TreeModelM1_constructible

/-- The V-basis model datum has an injective place map (reuse). -/
theorem sourceModelM1_vBasis_constructible :
    ∃ D : S3133ModelPlaceToModDatum, Function.Injective D.placeOf :=
  S3133ModelM1_constructible

/-- The route residual with the M1 place-selection slot filled by the Option-B
in-model evidence; M0 and stage4 remain as explicit slots (as Props). -/
def firstTriangleRouteResidualModelM1
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (m0 : Prop) (stage4 : Prop) :
    FirstTriangleRouteResidual I where
  sameCIdentification := m0
  placeSelection := sourceModelM1Evidence
  stage4UnitMap := stage4

/-- The in-model-M1 route residual's place-selection slot is inhabited (Option-B). -/
theorem firstTriangleRouteResidualModelM1_placeSelection
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (m0 : Prop) (stage4 : Prop) :
    (firstTriangleRouteResidualModelM1 I m0 stage4).placeSelection :=
  sourceModelM1Evidence_holds

end LeanFormal.IUT.XiFPaper.S3139ModelM1DischargeActual

end
