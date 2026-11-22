import tmp.sheaf.xif.paper.S3043LocalHaarVolumeSignActual
import tmp.sheaf.xif.paper.S2959HalfIQHullCThetaUpperActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3043LocalHaarVolumeSignActual
open LeanFormal.IUT.XiFPaper.S2959HalfIQHullCThetaUpperActual
open LeanFormal.IUT.XiFPaper.S2958HalfIQHullCertificateActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3047QuantitativeHscalarActual

variable {l : PrimeGeFive} {V : Type*}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The S2959 actual CThetaPaper value for an ABC triple. -/
noncomputable def S3047CTheta (a b c : Nat) (habc : IsABCTriple a b c) : Real :=
  CThetaPaper fiveLabel 1 0 (S2959ActualDFpd a b c habc) 1 0 0

/-- The paper q-absolute-log factor at q = exp 1. -/
noncomputable def S3047Q : Real := paperQAbsLog fiveLabel 1

theorem S3047_CTheta_nonneg (a b c : Nat) (habc : IsABCTriple a b c) :
    0 <= S3047CTheta a b c habc := by
  unfold S3047CTheta
  rw [S2959_CThetaPaper_eq_theta_signed a b c habc]
  change 0 <= iqHullRealVolume (S2958WAt a b c) + 1
  exact add_nonneg (iqHullRealVolume_nonneg (S2958WAt a b c)) zero_le_one

theorem S3047_Q_nonneg : 0 <= S3047Q := by
  unfold S3047Q paperQAbsLog qNormFactor
  positivity

/-- Quantitative hscalar: the actual nonnegative Haar value V satisfies
`-V <= CThetaPaper * paperQAbsLog` for the S2959 actual parameters. -/
theorem S3047_hscalar (a b c : Nat) (habc : IsABCTriple a b c) :
    -actualC3LogShellTensorLogVolume C3 <=
      S3047CTheta a b c habc * S3047Q := by
  have hV : 0 <= actualC3LogShellTensorLogVolume C3 :=
    S3043_logVolume_nonneg C3
  have hC : 0 <= S3047CTheta a b c habc := S3047_CTheta_nonneg a b c habc
  have hQ : 0 <= S3047Q := S3047_Q_nonneg
  have hprod : 0 <= S3047CTheta a b c habc * S3047Q := mul_nonneg hC hQ
  linarith

#check S3047CTheta
#check S3047Q
#check S3047_CTheta_nonneg
#check S3047_hscalar
#print axioms S3047_hscalar

end LeanFormal.IUT.XiFPaper.S3047QuantitativeHscalarActual
end
