import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealSignedLogVolume

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2983SignedQPilotActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, mon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)

/-- Actual signed q-pilot value: minus the real log-volume of the possible
Theta-pilot image union. -/
noncomputable def S2983QSigned : Real :=
  I.sourceSignedImageLogVolume v R n

theorem S2983_qSigned_eq :
    S2983QSigned I v R n =
      -(I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)).toReal := rfl

theorem S2983_qSigned_nonpos : S2983QSigned I v R n <= 0 :=
  I.sourceSignedImageLogVolume_nonpos v R n

/-- The corpus (xi-f) signed comparison at the actual qSigned. -/
def S2983SignedComparison : Prop :=
  S2983QSigned I v R n <= I.sourceSignedHullLogVolume v R n

/-- Exact reduction: the comparison is equivalent to the real-parts
normalization of the hull by the possible-image union. -/
theorem S2983_comparison_iff_realParts_eq
    (hfin : I.sourceHullVolume v R n < ⊤) :
    S2983SignedComparison I v R n <->
      I.sourceRealHullVolume v R n =
        (I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)).toReal :=
  sourceSignedImageComparison_iff_realParts_eq I v R n hfin

theorem S2983_comparison_of_hullVolume_eq
    (heq : I.sourceHullVolume v R n =
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)) :
    S2983SignedComparison I v R n :=
  sourceSignedImageComparison_of_hullVolume_eq_imageVolume I v R n heq

/-- Conditional Card-HULLREAL signed certificate at the actual qSigned. -/
noncomputable def S2983SignedCertificate
    (hcomp : S2983SignedComparison I v R n)
    (hqneg : S2983QSigned I v R n < 0) :
    StepXIFiniteCertificate (SignedLabel l.value) :=
  sourceSignedHullCertificate (I := I) v R n (S2983QSigned I v R n) hcomp hqneg

#check S2983QSigned
#check S2983_qSigned_eq
#check S2983_qSigned_nonpos
#check S2983SignedComparison
#check S2983_comparison_iff_realParts_eq
#check S2983_comparison_of_hullVolume_eq
#check S2983SignedCertificate
#print axioms S2983_qSigned_eq
#print axioms S2983_comparison_iff_realParts_eq
#print axioms S2983SignedCertificate

end LeanFormal.IUT.XiFPaper.S2983SignedQPilotActual
end