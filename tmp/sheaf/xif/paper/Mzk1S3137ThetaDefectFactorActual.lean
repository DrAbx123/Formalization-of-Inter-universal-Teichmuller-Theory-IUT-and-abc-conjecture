/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1S3137ThetaPacketRawGapActual
import Mathlib.Tactic

/-! # P6-D4: S3137 theta-defect factor decomposition (single cluster) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1S3137ThetaDefectFactorActual

def packetFactor (packetTheta : Real) : Real := packetTheta
def rawFactor (rawHaarLog : Real) : Real := rawHaarLog
def thetaDefect (packetTheta rawHaarLog : Real) : Real :=
  packetFactor packetTheta + rawFactor rawHaarLog

theorem thetaDefect_eq_packet_add_raw (packetTheta rawHaarLog : Real) :
    thetaDefect packetTheta rawHaarLog = packetTheta + rawHaarLog := by
  unfold thetaDefect packetFactor rawFactor
  ring

theorem thetaDefect_eq_zero_iff_factors (packetTheta rawHaarLog : Real) :
    thetaDefect packetTheta rawHaarLog = 0 ↔
      packetFactor packetTheta = -rawFactor rawHaarLog := by
  unfold thetaDefect
  constructor <;> intro h <;> linarith

def defectFactorRows : List (String × String × String) :=
  [ ("thetaDefect_eq_packet_add_raw", "defect = packet + raw", "PROVED"),
    ("thetaDefect_eq_zero_iff_factors", "defect zero iff packetFactor = -rawFactor", "PROVED") ]
theorem defectFactorRows_length : defectFactorRows.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1S3137ThetaDefectFactorActual
