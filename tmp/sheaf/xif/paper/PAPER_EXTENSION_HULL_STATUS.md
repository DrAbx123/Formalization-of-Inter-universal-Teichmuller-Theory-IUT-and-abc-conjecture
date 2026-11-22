# Root extension product Theta hull: existing work status

## 1. Theta hull / measurable hull: DONE (actual)

* PaperRootExtensionProductHaarActual
  - RootExtensionProductCarrier := (b) -> rootNormedExtension T b
  - rootExtensionProductHaar := Measure.pi (rootExtensionHaar T b)
  - rootExtensionProductUnitBall
  - rootExtensionProductHaar_unitBall_pos_lt_top
  - rootExtensionProductNormalizedLog
* PaperRootExtensionThetaHullAuditActual
  - rootImageRadius
  - rootExtensionProductImageHull = coordinatewise closed balls
  - rootExtensionProductThetaImageSet_subset_imageHull (actual)
  - rootExtensionProductImageHull_subset_unitBall (under RootQUnitNormLeOne)
  - rootExtensionProductImageHull_measure_pos_lt_top (actual)
  - rootExtensionProductImageHullLog (actual)
* PaperRootExtensionThetaHullActual
  - rootExtensionProductThetaHull / ThetaHullLog (full unit ball; log 0)
* PaperRootExtensionFieldScalingHaarActual
  - rootExtensionProductFieldScaledHullLog actual

## 2. Norm bound: DONE (actual, conditional on RootQUnitNormLeOne)

* PaperRootExtensionNormBoundActual
  - RootQUnitNormLeOne
  - rootNormedElement_norm_le_one
  - rootNormedThetaValueInL_norm_le_one
  - rootExtensionProductNormBound_of_qUnit
  - rootExtensionProductThetaImageSet_subset_unitBall_of_qUnit

## 3. Normalized log of hull: DONE (actual)

* rootExtensionProductImageHullLog
* rootExtensionProductFieldScaledHullLog

## 4. qPilot comparison: EXACT GAP

No theorem found comparing rootExtensionProductImageHullLog to a qPilot
scalar.  S649RootThetaExtensionComparisonActual packages this as an exact
Prop (RootThetaHullLogComparison / extensionToCompletionHullMap).

## 5. PaperXiFSourceLink: CONDITIONAL / EXACT

* S650RootThetaXiFThetaSideActual
  - RootThetaExtensionHullXiFBridge
  - paperXiFSourceLinkOfRootThetaHull (conditional fields).
* PaperXiFInclusion.PaperXiFSourceLink still needs
  source_identifications, qPilotLogVolume_eq_paper, link_identification,
  link_implies_inclusion.

## 6. Additional actual: tensor hull carrier

* S653RootThetaTensorHullCarrierGapActual
  - RootThetaTensorHullCarrierGapAt (universe-lifted)
  - filled imageMap/imageSet/unitReference/lambdaHull for RootThetaProductCarrier
  - only MinimalRootThetaTensorHullCarrierGap := RootThetaRootNormBound
  - RootThetaRootNormBound is already proved by
    rootExtensionProductNormBound_of_qUnit under RootQUnitNormLeOne.

Do not rebuild theta hull / product Haar / norm bound / image hull log.
Next actual work: qPilot comparison and PaperXiFSourceLink fields.
