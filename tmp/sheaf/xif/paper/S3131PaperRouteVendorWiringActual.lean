import tmp.sheaf.xif.paper.S3131PaperRouteComparisonDataActual

/-! # S3131 paper route: vendor comparison payload wiring (CorollarySchema shape) -/

noncomputable section
open LeanFormal.IUT.XiFPaper.S3131PaperRouteComparisonDataActual

namespace LeanFormal.IUT.XiFPaper.S3131PaperRouteVendorWiringActual

/-- Build the vendor-shaped comparison payload from signed canonical readouts
(qSigned = signed q-pilot readout, thetaSigned = signed theta-hull readout). -/
def comparisonDataOf (theta q : Real) (hq : q < 0) (hle : q <= theta) :
    S3131PaperRouteComparisonData :=
  { thetaSigned := theta, qSigned := q,
    q_positive := by linarith,
    qSigned_le_thetaSigned := hle }

/-- Cor. 3.12 endpoint in magnitude form from the vendor-shaped payload. -/
theorem comparisonDataOf_magnitude (theta q : Real) (hq : q < 0) (hle : q <= theta) :
    -theta <= -q :=
  S3131PaperRouteComparisonData.magnitude_le (comparisonDataOf theta q hq hle)

#check comparisonDataOf_magnitude

end LeanFormal.IUT.XiFPaper.S3131PaperRouteVendorWiringActual
end