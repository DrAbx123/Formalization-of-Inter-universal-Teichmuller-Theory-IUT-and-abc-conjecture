import tmp.sheaf.xif.paper.S2780LineBundleABCBridgeActual
import tmp.sheaf.xif.paper.S2792NormalizedLineBundleBridge
import tmp.sheaf.xif.paper.S2833S2800HregionActual
import tmp.sheaf.xif.paper.S2838HeightComparisonReductionActual
import tmp.sheaf.xif.paper.S2752FinalHweightvolActual
import tmp.sheaf.xif.paper.S2714CThetaUpperInventoryActual
import tmp.sheaf.xif.paper.S2691CanonicalMultiplicativeCertificateActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2780LineBundleABCBridgeActual
open LeanFormal.IUT.XiFPaper.S2792NormalizedLineBundleBridge
open LeanFormal.IUT.XiFPaper.S2833S2800HregionActual
open LeanFormal.IUT.XiFPaper.S2838HeightComparisonReductionActual
open LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual
open LeanFormal.IUT.XiFPaper.S2714CThetaUpperInventoryActual
open LeanFormal.IUT.XiFPaper.S2691CanonicalMultiplicativeCertificateActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2917ThetaUpperObjectInventory

/-!
## S2917 inventory: theta/J upper estimate objects

### Two equivalent upper-estimate targets

1. S2780HeightGap eps:
   forall ABC triples, logHeight(abcRationalPoint) <= (1+eps) * S2780RegionVolume.

2. S2838ThetaUpperGap eps AJ:
   forall ABC triples,
     logHeight(abcJInvariant) <= 6*(1+eps)*S2792RegionVolume + AJ.

They are the same theta/J upper estimate written on the point-height side and on
the J-height side, with the normalization S2792RegionVolume = 1/2 *
S2780RegionVolume and the ABCInvariantHeight comparison S2838_height_le_Jlog.

### Existing actual pieces

* S2792_regionVolume_le_weight_add_D:
  S2792RegionVolume <= arithmeticWeight + S2792D.  This is the actual
  region/weight comparison (no height).
* S2833_region_volume:
  the normalized comparison-region volume equals S2792RegionVolume.
* S2833_hull_volume_zero: the half-IQ hull volume is zero.
* S2838_height_le_Jlog:
  abcJInvariant_logHeight_bounds_abcRationalPoint.1, the actual
  point-height/J-height comparison.
* S2838_additiveHeightComparison_of_thetaGap:
  S2838ThetaUpperGap implies the additive height/region comparison.
* S2752_hweightvol: the qPilot line-bundle hweightvol statement, actual.
* S2691Certificate: the actual multiplicative Tate certificate (local
  multiplicative reduction); it does NOT give a global theta/J upper bound.
* S2714CThetaUpperInventoryActual:
  S2714_sourceSignedHull_upper_zero and
  S2714_cThetaLowerBound_of_upper; these are conditional/local hull statements,
  not the global theta/J upper estimate.

### What is missing

The actual theta/J upper estimate is exactly S2780HeightGap / S2838ThetaUpperGap.
Neither is proved.  The inventory shows:

* the region volume is actual (S2833) and bounded by the weight (S2792);
* the J-height comparison is actual (S2838_height_le_Jlog);
* the missing input is the theta/J upper bound itself, not any carrier,
  volume, or local multiplicative certificate.

No upper estimate is fabricated.
-/

#check S2780HeightGap
#check S2780RegionWeightGap
#check S2792_regionVolume_le_weight_add_D
#check S2833_region_volume
#check S2833_hull_volume_zero
#check S2838ThetaUpperGap
#check S2838_height_le_Jlog
#check S2838_additiveHeightComparison_of_thetaGap
#check S2752_hweightvol
#check S2691Certificate
#check S2714_sourceSignedHull_upper_zero
#check S2714_cThetaLowerBound_of_upper

end LeanFormal.IUT.XiFPaper.S2917ThetaUpperObjectInventory
end
