import tmp.sheaf.xif.paper.S3044HscalarBySignActual
import tmp.sheaf.xif.paper.S3034PacketScalarBoundActual
import tmp.sheaf.xif.paper.S3045CThetaPaperNonnegCounterexample
import tmp.sheaf.xif.paper.S3018C3TensorPacketLogVolumeFormula
import tmp.sheaf.xif.paper.S3043LocalHaarVolumeSignActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3044HscalarBySignActual
open LeanFormal.IUT.XiFPaper.S3034PacketScalarBoundActual
open LeanFormal.IUT.XiFPaper.S3045CThetaPaperNonnegCounterexample
open LeanFormal.IUT.XiFPaper.S3018C3TensorPacketLogVolumeFormula
open LeanFormal.IUT.XiFPaper.S3043LocalHaarVolumeSignActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.N8Closure.C3Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S3046PacketVolumeLowerBoundActual

variable (R : S1280RemainingClauses fiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)
variable (D : SourcePilotRegionDonors
  (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat))

/-- If the CThetaPaper q-product is nonnegative, hscalar follows from the
unconditional nonnegativity of the packet log-volume. -/
theorem S3046_hscalar_of_product_nonneg
    (logQ : Real) (a b c : Nat)
    (hC : 0 <= CThetaPaper fiveLabel logQ 0 S2990ActualDFpdActual.S2990DFpd
      (S2990ActualDFpdActual.S2990FFpd a b c) 0 0 *
        paperQAbsLog fiveLabel logQ) :
    S3034Hscalar R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat D logQ a b c :=
  S3044_hscalar_of_CTheta_nonneg (R := R) (redCompat := redCompat) (hredCompat := hredCompat) (torCompat := torCompat) (htorCompat := htorCompat) (orbCompat := orbCompat) (horbCompat := horbCompat) (secCompat := secCompat) (hsecCompat := hsecCompat) (cusCompat := cusCompat) (hcusCompat := hcusCompat) (D := D) logQ a b c hC

/-- Exact missing lower bound for the S3045 parameters: the packet log-volume
must dominate the positive number -CThetaPaper*paperQAbsLog. -/
def S3046MissingLower (logQ : Real) (a b c : Nat) : Prop :=
  - CThetaPaper fiveLabel logQ 0 S2990ActualDFpdActual.S2990DFpd
      (S2990ActualDFpdActual.S2990FFpd a b c) 0 0 *
        paperQAbsLog fiveLabel logQ <=
    actualC3LogShellTensorLogVolume
      (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat D)

/-- For the S3045 counterexample parameters the required lower bound is
strictly positive: CThetaPaper is negative and paperQAbsLog is positive. -/
theorem S3046_S3045_required_pos :
    0 < - CThetaPaper fiveLabel S3045LogQ 0 S2990ActualDFpdActual.S2990DFpd
      (S2990ActualDFpdActual.S2990FFpd 1 2 3) 0 0 *
        paperQAbsLog fiveLabel S3045LogQ := by
  have hCneg : CThetaPaper fiveLabel S3045LogQ 0 S2990ActualDFpdActual.S2990DFpd
      (S2990ActualDFpdActual.S2990FFpd 1 2 3) 0 0 < 0 := S3045_CThetaPaper_neg
  have hQpos : 0 < paperQAbsLog fiveLabel S3045LogQ := by
    unfold paperQAbsLog
    have h5 : (0 : Real) < (fiveLabel.value : Real) := by norm_num [fiveLabel]
    have h2 : (0 : Real) < 2 * (fiveLabel.value : Real) := by linarith
    have hfac : (0 : Real) < 1 / (2 * (fiveLabel.value : Real)) := by positivity
    exact mul_pos hfac S3045_logQ_pos
  have hprod : CThetaPaper fiveLabel S3045LogQ 0 S2990ActualDFpdActual.S2990DFpd
      (S2990ActualDFpdActual.S2990FFpd 1 2 3) 0 0 *
        paperQAbsLog fiveLabel S3045LogQ < 0 :=
    mul_neg_of_neg_of_pos hCneg hQpos
  linarith

#check S3046_hscalar_of_product_nonneg
#check S3046MissingLower
#check S3046_S3045_required_pos

end LeanFormal.IUT.XiFPaper.S3046PacketVolumeLowerBoundActual
end