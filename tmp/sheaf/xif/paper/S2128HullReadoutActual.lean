import tmp.sheaf.xif.PaperSignedHull
noncomputable section
set_option maxHeartbeats 1000000
namespace LeanFormal.IUT.XiFPaper.S2128HullReadoutActual
open LeanFormal.IUT
variable {X : Type} {label : Type} [Fintype label]
variable (P : PaperSignedHull X label)
/-- Actual finiteness of the ambient signed hull log-volume. -/
theorem s2128_ambient_hull_logVolume_lt_top :
    P.ambient.logVolume P.ambient.hull < ⊤ :=
  PaperSignedHull.ambient_hull_logVolume_lt_top P
/-- Actual direction H <= -vol(image): the signed hull log-volume is at most
the negative image-union log-volume. -/
theorem s2128_signedHull_le_neg_image_toReal
    (himg : P.ambient.logVolume P.ambient.imageSet < ⊤) :
    P.signedHullLogVolume ≤ -(P.ambient.logVolume P.ambient.imageSet).toReal :=
  PaperSignedHull.signedHullLogVolume_le_neg_image_toReal P himg
/-- Actual sign range: H = -average <= 0. -/
theorem s2128_signedHull_nonpos : P.signedHullLogVolume ≤ 0 :=
  PaperSignedHull.signedHullLogVolume_nonpos P
/-- Exact missing normalization to identify H with log Theta; this is not
proved by the hull interface alone. -/
def s2128HullThetaNormalization (thetaLog : Real) : Prop :=
  P.signedHullLogVolume = thetaLog
/-- If the paper Q <= H side is supplied as the exact log comparison
`qPilotLog ≤ thetaLog`, the hull normalization yields Q <= H. -/
theorem s2128_qPilot_le_signedHull_of_normalization
    {qPilotLog thetaLog : Real}
    (hQ : qPilotLog ≤ thetaLog)
    (hH : s2128HullThetaNormalization P thetaLog) :
    qPilotLog ≤ P.signedHullLogVolume :=
  by simpa [s2128HullThetaNormalization] using (hH.symm ▸ hQ)
#print axioms s2128_ambient_hull_logVolume_lt_top
#print axioms s2128_signedHull_le_neg_image_toReal
#print axioms s2128_signedHull_nonpos
#print axioms s2128_qPilot_le_signedHull_of_normalization
end LeanFormal.IUT.XiFPaper.S2128HullReadoutActual
end
