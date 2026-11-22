/-!
# S3139: prior-art audit 2 — model-route evidence tree (policy §7.9; data only)

Lead task: consume the existing tree model + StepXI/CardHull/CardAMPL assets in the
first-triangle composition, and update the residual list with Option-B in-model M1
evidence.  Prior-art check results (grep-first; file:line -> decision):

* tmp/sheaf/xif/paper/S3133ExistingModelAdaptationActual.lean (EXIT=0, results:159686)
  = the approved single adaptation layer over the EXISTING model:
  S3133TreeModelInput:48, S3133TreeModelRealization:52, S3133TreeModelHaarData:57,
  S3133TreeModelHaarData_scaling:66, S3133TreeModel_theta_q:72,
  S3133TreeModelPlaceToModDatum:85, S3133TreeModelM1Datum:95,
  S3133TreeModelM1_constructible:103, S3133TreeModelQVFam_descent:111,
  S3133TreeModelBaseUnitScaling:118 -> REUSE (Option-B in-model M1 + M2b).
* LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceUnitRegionHaarDataActual.lean
  sourceHaarActualFamily:322, sourceHaarActualOriginalInput:346,
  sourceHaarActualImageRealization:374, sourceHaarActualData:416 ->
  REUSE through the S3133 adaptation layer (no re-proof, no rebuild).
* tmp/sheaf/xif/paper/S3135ModelSkeletonInterfaceActual.lean (EXIT=0)
  S3135ModelHullPoint:51, S3135ModelHullHaar:54, S3135ModelUnitRegionHaarData:59,
  S3135ModelHaar_scaling_image_eq:98, s3135_modelBaseUnit:130,
  s3135_modelBaseUnit_norm_one:137 -> REUSE (model hull/Haar/scaling interface;
  the Haar unit-scalar set equality does not involve C3 comparison).
* tmp/sheaf/xif/paper/S3133ModelM1PlaceToModActual.lean (EXIT=0, results:155535)
  S3135ModelVMod:29, modelPlaceToMod:33, S3133ModelPlaceToModDatum:37,
  modelPlaceToModDatum:46, modelPlaceToMod_injective:54,
  S3133ModelM1_constructible:59 -> REUSE (V-basis in-model M1 datum).
* LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/CardHullRealSignedLogVolume.lean
  sourceSignedHullLogVolume:114, sourceSignedImageLogVolume:123,
  sourceSignedHullLogVolume_nonpos:129, sourceSignedImageLogVolume_nonpos:135,
  sourceSignedHullLogVolume_le_sourceSignedImageLogVolume:215,
  sourceSignedImageComparison_iff_realParts_eq:231 -> REUSE (fourth-triangle hull side,
  (xi-f) direction already proven in-tree; hull vs image signed comparison).
* LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/CardAMPLThetaBoundSupply.lean
  CardAMPLThetaBoundSupply:78, realVolume_le:94, ofReal_le_theta_of_imageSet_lower:101,
  cor312Conclusion:193, cardAMPLThetaBoundSupply:214 -> REUSE (supply interface and
  its Cor 3.12 conclusion; do not duplicate).
DECISION: Option-B in-model M1 discharged by reuse (S3133TreeModelM1Datum /
modelPlaceToModDatum); the fourth-triangle hull side is available in-model via CardHull;
general FT.M1 (arbitrary frozen input) remains OPEN; capsule-label link, M0, stage4
unit map, fourth-triangle arithmetic inputs remain OPEN.

**Component, not paper object.**  Registry frozen 13129; no registry edits.
No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.S3139PriorArtAudit2Actual

/-- Model-route prior-art reuse entries: (file:line, names, decision). -/
def modelRoutePriorArt : List (String × String × String) :=
  [ ("S3133ExistingModelAdaptationActual.lean:48-118",
      "S3133TreeModelInput/Realization/HaarData/_scaling/_theta_q/M1Datum/M1_constructible/QVFam_descent/BaseUnitScaling",
      "REUSE (Option-B in-model M1 + M2b adaptation layer)"),
    ("SourceUnitRegionHaarDataActual.lean:322/346/374/416",
      "sourceHaarActualFamily/OriginalInput/ImageRealization/Data",
      "REUSE through S3133 adaptation layer (no rebuild)"),
    ("S3135ModelSkeletonInterfaceActual.lean:51-150",
      "S3135ModelHullPoint/HullHaar/UnitRegionHaarData/Haar_scaling_image_eq/modelBaseUnit",
      "REUSE (model hull/Haar/scaling)"),
    ("S3133ModelM1PlaceToModActual.lean:29-61",
      "S3135ModelVMod/modelPlaceToMod/ModelPlaceToModDatum/modelPlaceToModDatum/_injective/S3133ModelM1_constructible",
      "REUSE (V-basis in-model M1)"),
    ("CardHullRealSignedLogVolume.lean:114/123/215/231",
      "sourceSignedHullLogVolume/ImageLogVolume/_le_sourceSignedImageLogVolume/_iff_realParts_eq",
      "REUSE (fourth-triangle hull side, xi-f direction proven in-tree)"),
    ("CardAMPLThetaBoundSupply.lean:78/94/193/214",
      "CardAMPLThetaBoundSupply/realVolume_le/cor312Conclusion/cardAMPLThetaBoundSupply",
      "REUSE (supply interface + Cor 3.12 conclusion; no duplicate)") ]

end LeanFormal.IUT.XiFPaper.S3139PriorArtAudit2Actual
