/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.gogopex.Iut.Stage1.PilotComparison

/-! # A520: S3137 q/Theta readings => Gogopex signed comparison (Corollary312Inequality) -/

noncomputable section

namespace LeanFormal.IUT.Objects.S3137GogopexBridge

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open Iut RealLineCopy

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The signed q-side pilot log-volume of the Gogopex package, from the actual q-pilot
reading `-|log q|`: stored magnitude is `-qPilotLogVolumeReading P`. -/
def s3137QSignedPilot (P : PaperQPilotObjectActual (l := l) (I := I)) : Stage1.PilotLogVolume :=
  { side := Stage1.PilotSide.q, value := -qPilotLogVolumeReading P }

/-- The signed Theta-side pilot log-volume of the Gogopex package, from the actual Theta
hull log-volume reading: stored magnitude is `-thetaPilotHullLogVolumeReal C3`. -/
def s3137ThetaSignedPilot : Stage1.PilotLogVolume :=
  { side := Stage1.PilotSide.theta, value := -thetaPilotHullLogVolumeReal C3 }

/-- **S3137 comparison ⇒ Gogopex Stage-1 comparison**: from the named candidate
`qThetaPilotLogVolumeComparison` and strict negativity of the q reading, build the Gogopex
`Stage1Comparison` package (sides, positivity, and the signed `Corollary312Inequality`). -/
def stage1ComparisonOfS3137 (P : PaperQPilotObjectActual (l := l) (I := I))
    (hcmp : qThetaPilotLogVolumeComparison C3 P)
    (hqneg : qPilotLogVolumeReading P < 0) : Stage1.Stage1Comparison where
  theta := s3137ThetaSignedPilot C3
  q := s3137QSignedPilot P
  theta_side := rfl
  q_side := rfl
  q_positive := by
    show 0 < -qPilotLogVolumeReading P
    linarith
  comparison := by
    show -(-thetaPilotHullLogVolumeReal C3) ≥ -(-qPilotLogVolumeReading P)
    simpa using hcmp

/-- The bridge's comparison is exactly the Gogopex `Corollary312Inequality` between the
signed q/Theta readings. -/
theorem corollary312Inequality_of_s3137 (P : PaperQPilotObjectActual (l := l) (I := I))
    (hcmp : qThetaPilotLogVolumeComparison C3 P)
    (hqneg : qPilotLogVolumeReading P < 0) :
    Stage1.Corollary312Inequality
      (s3137ThetaSignedPilot C3) (s3137QSignedPilot P) :=
  (stage1ComparisonOfS3137 C3 P hcmp hqneg).comparison

/-- The comparison, unpacked, is the signed real inequality `-|log q| <= -|log Theta|`
for the S3137 readings. -/
theorem s3137_signed_real_inequality (P : PaperQPilotObjectActual (l := l) (I := I))
    (hcmp : qThetaPilotLogVolumeComparison C3 P)
    (hqneg : qPilotLogVolumeReading P < 0) :
    -(s3137ThetaSignedPilot C3).value ≥ -(s3137QSignedPilot P).value :=
  corollary312Inequality_of_s3137 C3 P hcmp hqneg

end LeanFormal.IUT.Objects.S3137GogopexBridge
