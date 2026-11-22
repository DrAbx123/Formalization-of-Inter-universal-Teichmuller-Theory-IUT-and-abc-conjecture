import tmp.sheaf.xif.paper.Node09S3135F4InvestigationActual
import tmp.sheaf.xif.paper.S3135FinalResidualActual

noncomputable section
open scoped BigOperators ENNReal
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2614CompactnessScalingActual
open LeanFormal.IUT.XiFPaper.S3135ScalingNormalizationActual
open LeanFormal.IUT.XiFPaper.S3135LogShellValueGroupActual
open LeanFormal.IUT.XiFPaper.S3135F5ActualReductionActual
open LeanFormal.IUT.XiFPaper.S3135ActualF4LogShellDegreeActual
open LeanFormal.IUT.XiFPaper.S3135FinalResidualActual
open LeanFormal.IUT.XiFPaper.Node09S3135F4InvestigationActual

namespace LeanFormal.IUT.XiFPaper.Node09S3135CanonicalDInvestigationActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
variable (C : I.SourceOneCircUCompactness v R n)

/-- With the canonical compactness D, scaling log-degree zero is automatic, so
under the point-faithfulness card Card P is exactly the ABC-strength additive
bound.  This shows Card P is not discharged by the canonical D alone. -/
theorem cardP_iff_additiveBound_canonicalD
    (hpt : S3135PointLogShellFaithfulness I v R) :
    S3135ActualPointWeightCard I v R n
        (I.sourceOModuleCompactness_haarData v R n C) (abcSourcePoint I v R) ↔
      ABCHeightWeightAdditiveBoundV2 :=
  s3135_pointWeightCard_iff_additiveBound I v R n
    (I.sourceOModuleCompactness_haarData v R n C) hpt
    (s3135_scalingLogDegreeZero_compactness I v R n C)

/-- Exact status for the canonical compactness D. -/
def Node09S3135CanonicalDStatus : List String :=
  [ "for D = sourceOModuleCompactness_haarData v R n C, S3135ScalingLogDegreeZero is actual (scaling is literally 1)",
    "S3135PointLogShellFaithfulness depends only on I, v, R and is independent of D; no instance of SourceOneCircUCompactness supplies it, and the only constructed value-layer model refutes it",
    "under the canonical D and hpt, Card P is equivalent to ABCHeightWeightAdditiveBoundV2 (cardP_iff_additiveBound_canonicalD), hence ABC-strength; canonical D alone cannot discharge Card P",
    "no fake; the canonical D discharges only the F4 (b) scaling card, not PointFaithfulness or Card P" ]

end LeanFormal.IUT.XiFPaper.Node09S3135CanonicalDInvestigationActual
