# S975: S957 density via region images

Date: 2026-10-30. Region-image reduction.

## Actual region-image route

rootThetaRegionImageInLValued j :=
  qVFamToLValued '' rootThetaRegion(cRoot, j).

paperPossibleRegionImageUnion := union_j rootThetaRegionImageInLValued j.

qPilotRegionImage_subset_regionUnion:
  qVFamToLValued '' qPilotPaperRegion
    ⊆ paperPossibleRegionImageUnion,
because qPilotPaperRegion = rootThetaRegion at oneLabel.

## Exact remaining condition

S975RegionImageSubsetPaperTensorHull D:
  paperPossibleRegionImageUnion ⊆ paperTensorHull D.

s957ThetaImageDenseInQPilot_of_regionImageSubset:
  this region-union containment implies S957ThetaImageDenseInQPilot D.

## Gap

S975DensityExactGap D := S957ThetaImageDenseInQPilot D remains as the exact
Prop when the region-union containment is not supplied.

No density is fabricated; no equality/scaling.
