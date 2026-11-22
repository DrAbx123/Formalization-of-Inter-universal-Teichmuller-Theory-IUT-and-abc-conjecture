import tmp.sheaf.xif.paper.S2951ThetaSignedActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiring

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2951ThetaSignedActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2960ThetaHullIdentification

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- Exact identification target: a real hullVolume equals the S2951 thetaSigned
(sourceSignedHullLogVolume). -/
def S2960HullVolumeIdentification
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hullVolume : Real) : Prop :=
  hullVolume = S2951ThetaSigned v R n

/-- Actual: S2951ThetaSigned is the negative real hull volume, by definition. -/
theorem S2960_thetaSigned_eq_neg_realHull
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    S2951ThetaSigned v R n = -I.sourceRealHullVolume v R n := rfl

/-- Actual identification with hullVolume := -sourceRealHullVolume. -/
theorem S2960_identification_of_realHull
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    S2960HullVolumeIdentification v R n (-I.sourceRealHullVolume v R n) :=
  rfl

/-!
## First error / missing object

There is no file or definition named S2958 in the current D:\lean tree, so the
literal S2958 hullVolume field cannot be referenced.  The actual objects are:

* S2951ThetaSigned v R n = I.sourceSignedHullLogVolume v R n
  = -(I.sourceRealHullVolume v R n), where
  I.sourceRealHullVolume v R n = (I.sourceHullVolume v R n).toReal;
* I.sourceHullVolume is ENNReal, not Real.

Thus an identification S2958 hullVolume = S2951ThetaSigned can only be proved
after S2958 is supplied with:
* a real hullVolume field, and
* an equality/normalization hullVolume = -(I.sourceHullVolume v R n).toReal.

Without S2958, the exact first missing object is the S2958 definition itself.
The actual identification with -sourceRealHullVolume is proved above; no
metric or normalization is invented.
-/

#check S2960HullVolumeIdentification
#check S2960_thetaSigned_eq_neg_realHull
#check S2960_identification_of_realHull
#print axioms S2960_identification_of_realHull

end LeanFormal.IUT.XiFPaper.S2960ThetaHullIdentification
end
