# S978: finite-carrier paperTensorHull and density

Date: 2026-10-30. Finite carrier S976/Qp^d, no point-set union.

## Finite carrier

Given L : S965CarrierLinearization T b,
  e : FinalLValuedCarrier T b ~ Qp^(L.d).

finitePossibleRegionImageUnion := e '' paperPossibleRegionImageUnion.
finitePaperTensorHull := closure (finitePossibleRegionImageUnion) in the
actual finite Qp^d topology (S970/S976).  No fake topology.

## Actual containment

finiteQPilotImage_subset_finiteHull:
  e '' (qVFamToLValued '' qPilotPaperRegion)
    subset finitePaperTensorHull,
using S975 qPilotRegionImage_subset_regionUnion and subset_closure.

## Exact minimal bridge to S957 density

S978FiniteHullBridge:
  finitePaperTensorHull subset e '' paperTensorHull T b D.

s957ThetaImageDenseInQPilot_of_finiteHullBridge:
  S978FiniteHullBridge -> S957ThetaImageDenseInQPilot D,
using injectivity of e.

S978DensityExactGap D records S957ThetaImageDenseInQPilot D when the bridge is
not supplied.

No equality/scaling; no fake topology; no point-set union.
