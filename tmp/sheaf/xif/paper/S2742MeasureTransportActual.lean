import tmp.sheaf.xif.paper.S2725ThetaImageHullActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealSignedLogVolume

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2742MeasureTransportActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- Actual measure/volume transport for the S2725 source theta image and hull. -/
structure S2742ImageHullMeasureTransport
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) where
  imageVolume : ENNReal
  hullVolume : ENNReal
  imageVolume_eq : imageVolume =
    I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)
  hullVolume_eq : hullVolume = I.sourceHullVolume v R n
  image_le_hull : imageVolume <= hullVolume
  hull_eq_signed : I.sourceSignedHullLogVolume v R n =
    -(I.sourceRealHullVolume v R n)

noncomputable def s2742ImageHullMeasureTransport
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    S2742ImageHullMeasureTransport (I := I) v R n where
  imageVolume := I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)
  hullVolume := I.sourceHullVolume v R n
  imageVolume_eq := rfl
  hullVolume_eq := rfl
  image_le_hull := I.sourceHullVolume_ge_imageVolume v R n
  hull_eq_signed := I.sourceSignedHullLogVolume_eq_neg_hullSetVolume v R n

theorem s2742_image_volume_le_hull (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) <=
      I.sourceHullVolume v R n :=
  I.sourceHullVolume_ge_imageVolume v R n

/-- Actual signed-log transport: the hull signed log is at most the image
signed log (the hull contains the image). -/
theorem s2742_signedHullLog_le_signedImageLog (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) :
    I.sourceSignedHullLogVolume v R n <=
      I.sourceSignedImageLogVolume v R n :=
  I.sourceSignedHullLogVolume_le_sourceSignedImageLogVolume v R n hfin

/-- Actual monotonicity transfer: any subset of the actual source hull has
source set volume at most the hull volume. -/
theorem s2742_subset_hull_volume_le (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    {S : Set (I.ThetaPilotPoint v)}
    (hS : S ⊆ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))) :
    I.sourceSetVolume v S <= I.sourceHullVolume v R n :=
I.sourceSetVolume_mono v hS

#check S2742ImageHullMeasureTransport
#check s2742ImageHullMeasureTransport
#check s2742_image_volume_le_hull
#check s2742_signedHullLog_le_signedImageLog
#check s2742_subset_hull_volume_le
#print axioms s2742ImageHullMeasureTransport

end LeanFormal.IUT.XiFPaper.S2742MeasureTransportActual
end
