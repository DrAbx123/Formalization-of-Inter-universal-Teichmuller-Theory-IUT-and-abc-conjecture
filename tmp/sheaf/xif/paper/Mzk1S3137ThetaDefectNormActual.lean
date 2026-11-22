/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1S3137ThetaPacketRawGapActual
import Mathlib.Tactic

/-! # P6-C3: S3137 raw-vs-packet signed defect (single cluster, GAP interface) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1S3137ThetaDefectNormActual

/-- Signed defect between packet theta and S3137 raw Haar log. -/
def thetaDefect (packetTheta rawHaarLog : Real) : Real :=
  packetTheta + rawHaarLog

/-- The named gap is exactly vanishing absolute defect. -/
theorem abs_thetaDefect_eq_zero_iff (packetTheta rawHaarLog : Real) :
    |thetaDefect packetTheta rawHaarLog| = 0 ↔
      LeanFormal.IUT.XiFPaper.Mzk1S3137ThetaPacketRawGapActual.GapThetaPacketRaw
        packetTheta rawHaarLog := by
  unfold thetaDefect LeanFormal.IUT.XiFPaper.Mzk1S3137ThetaPacketRawGapActual.GapThetaPacketRaw
  rw [abs_eq_zero]
  constructor <;> intro h <;> linarith

def defectRows : List (String × String × String) :=
  [ ("thetaDefect", "packet + raw", "DEF"),
    ("abs_thetaDefect_eq_zero_iff", "defect zero iff GAP", "PROVED") ]
theorem defectRows_length : defectRows.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1S3137ThetaDefectNormActual
