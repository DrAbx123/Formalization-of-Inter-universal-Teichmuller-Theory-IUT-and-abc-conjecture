import Mathlib

/-! # S3131 paper route: vendor-adapted comparison payload (CorollarySchema shape)

Adapted from vendor Iut/Stage1/CorollarySchema.lean:55-83 (source reference only):
a signed comparison payload for the Cor. 3.12 endpoint.  In our route the reals are
the signed canonical readouts: qSigned corresponds to S3131CanonicalRootedQC and
thetaSigned to S3131CanonicalRootedHC (signed convention: log-volume of regions
inside O_hol is negative). -/

namespace LeanFormal.IUT.XiFPaper.S3131PaperRouteComparisonDataActual

structure S3131PaperRouteComparisonData where
  thetaSigned : Real
  qSigned : Real
  q_positive : 0 < -qSigned
  qSigned_le_thetaSigned : qSigned <= thetaSigned

namespace S3131PaperRouteComparisonData

theorem qSigned_neg (d : S3131PaperRouteComparisonData) : d.qSigned < 0 := by
  linarith [d.q_positive]

theorem qSigned_le_theta (d : S3131PaperRouteComparisonData) : d.qSigned <= d.thetaSigned :=
  d.qSigned_le_thetaSigned

/-- Cor. 3.12 endpoint inequality in magnitude form: |theta| <= |q|. -/
theorem magnitude_le (d : S3131PaperRouteComparisonData) :
    -d.thetaSigned <= -d.qSigned := by
  linarith [d.qSigned_le_thetaSigned]

end S3131PaperRouteComparisonData

#check S3131PaperRouteComparisonData.magnitude_le

end LeanFormal.IUT.XiFPaper.S3131PaperRouteComparisonDataActual