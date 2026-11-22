import tmp.sheaf.xif.paper.S3133ModelVBasisActual
import tmp.sheaf.xif.paper.S3137ModelPlaceToModConstructionActual
import LeanFormal.IUT.Audit.Status

/-! # S3137: model placeToMod literal wiring (qpilot frozen ModelVBasis)

Wires the constructible placeToMod field data to qpilot's frozen model place
basis S3133ModelVBasisActual (S3135ModelPlace := Sum (Fin 1) (Fin 1),
S3135ModelV, vFive, vInf, vFive_ne_vInf).  The literal map and faithfulness
instance are constructed here; no data fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3137ModelPlaceToModWiringActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3133ModelVBasisActual
open LeanFormal.IUT.XiFPaper.S3137ModelPlaceToModActual
open LeanFormal.IUT.XiFPaper.S3137ModelPlaceToModConstructionActual
open LeanFormal.IUT.Audit

/-- The two model place types agree definitionally (both Sum (Fin 1) (Fin 1)). -/
theorem modelPlace_eq_S3135ModelPlace : ModelPlace = S3135ModelPlace :=
  rfl

/-- The literal placeToMod field data for the model V: places -> S3135ModelV via
vFive and vInf, with faithfulness. -/
noncomputable def modelPlaceToModDataS3135 : ModelPlaceToModData S3135ModelV :=
  modelPlaceToModDataOfDistinct vFive vInf vFive_ne_vInf

/-- Faithfulness instance of the literal model placeToMod data. -/
theorem modelPlaceToModDataS3135_faithful :
    Function.Injective (modelPlaceToModDataS3135).placeToV :=
  (modelPlaceToModDataS3135).faithful

/-- The nonarchimedean model place maps to vFive. -/
@[simp] theorem modelPlaceToModDataS3135_inl (x : Fin 1) :
    (modelPlaceToModDataS3135).placeToV (Sum.inl x) = vFive :=
  rfl

/-- The archimedean model place maps to vInf. -/
@[simp] theorem modelPlaceToModDataS3135_inr (x : Fin 1) :
    (modelPlaceToModDataS3135).placeToV (Sum.inr x) = vInf :=
  rfl

/-- The two place images are distinct (the literal data is faithful). -/
theorem modelPlaceToModDataS3135_images_ne :
    (modelPlaceToModDataS3135).placeToV (Sum.inl (0 : Fin 1)) ≠
      (modelPlaceToModDataS3135).placeToV (Sum.inr (0 : Fin 1)) := by
  rw [modelPlaceToModDataS3135_inl, modelPlaceToModDataS3135_inr]
  exact vFive_ne_vInf

end LeanFormal.IUT.XiFPaper.S3137ModelPlaceToModWiringActual

namespace LeanFormal.IUT.Audit

/-- INDEX: literal model placeToMod data (wired to qpilot frozen basis). -/
def S3137ModelPlaceToModWiringRecord : Obligation :=
  { id := "INDEX.MODEL.place-to-mod-literal"
    source := "qpilot S3133ModelVBasisActual (EXIT0 1332): S3135ModelPlace, S3135ModelV, vFive, vInf, vFive_ne_vInf; S3137ModelPlaceToModConstructionActual"
    status := VerificationStatus.interface
    note := "CONSTRUCTED: modelPlace_eq_S3135ModelPlace (rfl); modelPlaceToModDataS3135 = modelPlaceToModDataOfDistinct vFive vInf vFive_ne_vInf : ModelPlaceToModData S3135ModelV; modelPlaceToModDataS3135_faithful (injectivity); place images vFive/vInf with images_ne. This is the literal explicit placeToMod field data for the model; consumers qpilot model assembly/abc wrapper/from-scratch model. Not a residual itself."
    dependsOn := ["S3133ModelVBasisActual", "S3137ModelPlaceToModConstructionActual"] }

end LeanFormal.IUT.Audit