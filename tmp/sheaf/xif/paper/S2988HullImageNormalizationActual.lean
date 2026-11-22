import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiring

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2988HullImageNormalizationActual

variable {l : PrimeGeFive}
variable {V : Type*}
variable (I : Theorem311Source.OriginalInput l V)

/-- Exact ENNReal normalization target: hull volume equals the volume of the
union of possible theta-pilot images. -/
def S2988HullImageNormalization (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : Prop :=
  I.sourceHullVolume v R n =
    I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)

/-- Exact real normalization target. -/
def S2988HullImageNormalizationReal (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : Prop :=
  I.sourceRealHullVolume v R n =
    (I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)).toReal

/-- Actual half: the image-union volume is at most the hull volume. -/
theorem S2988_imageVolume_le_hullVolume (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) <=
      I.sourceHullVolume v R n :=
  I.sourceHullVolume_ge_imageVolume v R n

/-- Actual real half, unconditionally from the ENNReal inequality and
`toReal` monotonicity. -/
theorem S2988_imageVolume_toReal_le_hullVolume (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) :
    (I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)).toReal <=
      I.sourceRealHullVolume v R n :=
  ENNReal.toReal_mono (ne_top_of_lt hfin) (S2988_imageVolume_le_hullVolume I v R n)

#check S2988HullImageNormalization
#check S2988HullImageNormalizationReal
#check S2988_imageVolume_le_hullVolume
#check S2988_imageVolume_toReal_le_hullVolume
#print axioms S2988_imageVolume_le_hullVolume
#print axioms S2988_imageVolume_toReal_le_hullVolume

end LeanFormal.IUT.XiFPaper.S2988HullImageNormalizationActual
end
