import tmp.sheaf.xif.paper.S2983SignedQPilotActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2983SignedQPilotActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2977CardHULLREALSignedActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)

abbrev S2977QSigned : Real := S2983QSigned I v R n

def S2977SignedComparison : Prop := S2983SignedComparison I v R n

theorem S2977_qSigned_eq :
    S2977QSigned I v R n =
      -(I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)).toReal := rfl

theorem S2977_comparison_iff_realParts_eq
    (hfin : I.sourceHullVolume v R n < ⊤) :
    S2977SignedComparison I v R n <->
      I.sourceRealHullVolume v R n =
        (I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)).toReal :=
  S2983_comparison_iff_realParts_eq I v R n hfin

noncomputable def S2977SignedCertificate
    (hcomp : S2977SignedComparison I v R n)
    (hqneg : S2977QSigned I v R n < 0) :
    StepXIFiniteCertificate (SignedLabel l.value) :=
  S2983SignedCertificate I v R n hcomp hqneg

/-- Exact missing normalization: hull real part equals the possible-image
union real part.  This is the only obstruction to the signed comparison. -/
def S2977HullImageNormalization : Prop :=
  I.sourceRealHullVolume v R n =
    (I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)).toReal

theorem S2977_comparison_of_normalization
    (hfin : I.sourceHullVolume v R n < ⊤)
    (h : S2977HullImageNormalization I v R n) :
    S2977SignedComparison I v R n :=
  (S2977_comparison_iff_realParts_eq I v R n hfin).mpr h

#check S2977QSigned
#check S2977SignedComparison
#check S2977_qSigned_eq
#check S2977_comparison_iff_realParts_eq
#check S2977SignedCertificate
#check S2977HullImageNormalization
#check S2977_comparison_of_normalization
#print axioms S2977_qSigned_eq
#print axioms S2977_comparison_iff_realParts_eq
#print axioms S2977SignedCertificate

end LeanFormal.IUT.XiFPaper.S2977CardHULLREALSignedActual
end