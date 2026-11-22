import tmp.sheaf.xif.paper.Mzk1ABCBridgeGap2ConsumerActual
import tmp.sheaf.xif.paper.S3133RealifiedQPilotLogVolumeActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Objects.ABCBridgeGap2
open LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

namespace LeanFormal.IUT.XiFPaper.Node09PM7SNamedActual

/-- Source-data route from P7 weighted q-ideal volume to the SNamed estimate:
if the comparison-region volume is bounded by the P7 weighted q-pilot volume
(-qPilotRealifiedLogVolume = sum of weighted local log magnitudes), and that
weighted volume is bounded by the arithmetic weight plus theta and D, then the
SNamed ENNReal estimate holds. -/
theorem SNamed_of_region_le_weightedQPilot
    {l : PrimeGeFive} (X : N8NativeInput l)
    [Fintype (Bad (nativePlaceSelection X.S))]
    {regionVolume : ENNReal} {eps weight theta D : Real}
    (hfin : regionVolume ≠ ⊤)
    (hR : 0 ≤ (1 + eps) * weight + theta + D)
    (hregion : regionVolume.toReal ≤ -qPilotRealifiedLogVolume X)
    (hweighted : -qPilotRealifiedLogVolume X ≤
      (1 + eps) * weight + theta + D) :
    SNamed regionVolume eps weight theta D :=
  gap2_ennreal_bound hfin hR (le_trans hregion hweighted)

/-- Exact source-data input for the P7 weighted-volume route. -/
def Node09PM7SNamedResidual : List String :=
  [ "-qPilotRealifiedLogVolume X = sum_b (qVEffectiveMultiplicity X b : Real) * log (residueNormBase b.1) is the P7 weighted q-ideal log-volume (S3133 qPilotRealifiedLogVolume_eq / qPilotRealifiedLogVolume_eq_neg_sum_localLogMagnitude)",
    "comparison (i): (comparison region volume).toReal <= -qPilotRealifiedLogVolume X, i.e. the value-monoid comparison-region volume is bounded by the P7 weighted q-ideal volume; no containment/volume comparison donor exists in the tree",
    "comparison (ii): -qPilotRealifiedLogVolume X <= (1+eps)*arithmeticWeight + theta + D; this is the remaining weighted q-ideal to arithmetic-weight estimate (paper-level IUT IV)",
    "SNamed_of_region_le_weightedQPilot composes (i) and (ii) into the SNamed ENNReal estimate; no inhabitant of (i)/(ii) is constructed",
    "no fake" ]

end LeanFormal.IUT.XiFPaper.Node09PM7SNamedActual
