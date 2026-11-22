import tmp.sheaf.xif.paper.S3137ModelPlaceToModActual
import LeanFormal.IUT.Audit.Status

/-! # S3137: model placeToMod faithfulness construction (task-72)

Constructive faithfulness lemma for the model placeToMod field: any two DISTINCT
model-V elements give an injective map from the two model places, hence an actual
ModelPlaceToModData.  This is the constructible half; the literal model V and its
two points (qpilot frozen S3135ModelV, vFive et al.) remain qpilot's data.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3137ModelPlaceToModConstructionActual

open LeanFormal.IUT.XiFPaper.S3137ModelPlaceToModActual
open LeanFormal.IUT.Audit

/-- The canonical map sending the two model places to two supplied points. -/
def modelPlaceMap {V : Type} (v0 v1 : V) : ModelPlace → V
  | Sum.inl _ => v0
  | Sum.inr _ => v1

/-- **Faithfulness lemma**: two distinct points give an injective place map. -/
theorem modelPlaceMap_injective {V : Type} (v0 v1 : V) (h : v0 ≠ v1) :
    Function.Injective (modelPlaceMap (V := V) v0 v1) := by
  intro x y hxy
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (Subsingleton.elim x y)
    | inr y => exact absurd hxy h
  | inr x =>
    cases y with
    | inl y => exact absurd hxy.symm h
    | inr y => exact congrArg Sum.inr (Subsingleton.elim x y)

/-- **Construct the model placeToMod field data** from two distinct points. -/
def modelPlaceToModDataOfDistinct {V : Type} (v0 v1 : V) (h : v0 ≠ v1) :
    ModelPlaceToModData V :=
  ModelPlaceToModData.ofInjective (modelPlaceMap v0 v1)
    (modelPlaceMap_injective v0 v1 h)

/-- The constructed place map takes the two places exactly to the two points. -/
@[simp] theorem modelPlaceToModDataOfDistinct_apply {V : Type} (v0 v1 : V)
    (h : v0 ≠ v1) (i : ModelPlace) :
    (modelPlaceToModDataOfDistinct v0 v1 h).placeToV i = modelPlaceMap v0 v1 i :=
  rfl

end LeanFormal.IUT.XiFPaper.S3137ModelPlaceToModConstructionActual

namespace LeanFormal.IUT.Audit

/-- INDEX: constructible placeToMod faithfulness. -/
def S3137ModelPlaceToModConstructionRecord : Obligation :=
  { id := "INDEX.MODEL.from-scratch-place-to-mod-faithful"
    source := "S3137ModelPlaceToModActual; IUT I Definition 3.1(b),(e)"
    status := VerificationStatus.interface
    note := "CONSTRUCTED CONDITIONAL: modelPlaceMap, modelPlaceMap_injective (two distinct V points give injective place map), modelPlaceToModDataOfDistinct (actual ModelPlaceToModData). EXACT MISSING: the literal model V and the two distinct points (qpilot frozen S3135ModelV/vFive). Not a residual by itself."
    dependsOn := ["S3137ModelPlaceToModActual"] }

end LeanFormal.IUT.Audit