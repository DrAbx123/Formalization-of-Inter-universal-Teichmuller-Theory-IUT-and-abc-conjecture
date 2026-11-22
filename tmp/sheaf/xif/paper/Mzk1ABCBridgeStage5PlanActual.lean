/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-! # A550: ABC Stage 5 plan (two hcomp gaps after Cor 3.12) -/

/-
Stage 5 = Cor 3.12 => ABC/height (IUTchIV/[ExpEst]); see coord/ROUTE-NECESSITY-A508.md.
Two content gaps (unique named gaps, abcbridge:Cor312EpsilonArithmeticComparison.twoNamedGaps):

1. height_le_normalizedRegionVolume (Gap 1)
   needs: height data of the ABC triple (Height.logHeight₁ / abcRationalPoint), the
   comparison region object (normalizedComparisonRegion over a hull/log-volume interface),
   and the height-vs-region estimate. Our assets: Cor312ToABCBridgeInterface,
   A503HeightRegionObjectActual (height/weight objects), A511HeightRegionGlueActual.
   Green: literal carrier/product-Haar rungs (A481/A483b/A482b) are on the 3.12 side only.

2. regionVolume_le_normalizedWeight (Gap 2)
   needs: region log-volume (ENNReal.toReal) compared with (1+eps)*arithmeticWeight + theta + D;
   our assets: A502HcompToRealAdapterActual (ENNReal/Real conversion lemmas),
   Cor312ToABCCards explicit constants, Takkun Diophantine constants (thm110/cor22,
   PNT/Chebyshev) as explicit constant sources. The estimate itself is the named gap.

Interfaces: Cor312ToABCBridgeInterface (carrier, hullData: IQHullLogVolumeInterface,
epsilonComparison: forall eps>0, Cor312EpsilonArithmeticComparison hullData eps);
consumer cor312ToABCBridge_heightBound uses exactly the two fields above.

Dispatch:
- abc (me): keep A502 adapter/constant plumbing green; write the Gap-2 arithmetic consumer
  with explicit constants, leaving the analytic estimate as the minimal named field.
- hull: construct the Gap-1 height region object over the actual hull interface
  (Mzk1LiteralHullObject / Mzk1HullDetObjectActual) and wire height data;
  report which object fields are still named.
- mainline: after 3.12 checks green, connect Cor312Conclusion -> bridge interface inputs.

NOTE: no Lean declarations yet in this file (planning only); adding fields requires the
actual signatures of Cor312EpsilonArithmeticComparison (read next round).
-/
