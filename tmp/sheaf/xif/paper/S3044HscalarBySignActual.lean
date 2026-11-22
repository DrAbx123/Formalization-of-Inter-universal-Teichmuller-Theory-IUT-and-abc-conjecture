import tmp.sheaf.xif.paper.S3034PacketScalarBoundActual
import tmp.sheaf.xif.paper.S3043LocalHaarVolumeSignActual
import tmp.sheaf.xif.paper.S3018C3TensorPacketLogVolumeFormula

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3034PacketScalarBoundActual
open LeanFormal.IUT.XiFPaper.S3025ActualThetaUpperAudit
open LeanFormal.IUT.XiFPaper.S3043LocalHaarVolumeSignActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S3018C3TensorPacketLogVolumeFormula
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.N8Closure.C3Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S3044HscalarBySignActual

variable (R : S1280RemainingClauses fiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)
variable (D : SourcePilotRegionDonors
  (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat))


local instance s3044Measurable :
    MeasurableSpace (C3LogShellTensorBlock
      (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat D)) := borel _

local instance s3044Borel :
    BorelSpace (C3LogShellTensorBlock
      (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat D)) := ⟨rfl⟩

/-- If the packet log-volume is nonnegative and CThetaPaper*paperQAbsLog is
nonnegative, hscalar follows. -/
theorem S3044_hscalar_of_nonneg
    (logQ : Real) (a b c : Nat)
    (hV : 0 <= actualC3LogShellTensorLogVolume
      (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat D))
    (hC : 0 <= CThetaPaper fiveLabel logQ 0 S2990ActualDFpdActual.S2990DFpd
      (S2990ActualDFpdActual.S2990FFpd a b c) 0 0 *
        paperQAbsLog fiveLabel logQ) :
    S3034Hscalar R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat D logQ a b c := by
  unfold S3034Hscalar S3025MissingThetaUpperScalar
  have hneg : - actualC3LogShellTensorLogVolume
      (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat D) <= 0 := by linarith
  exact le_trans hneg hC



/-- Actual hscalar from S3043: V >= 0 is unconditional, so only the
CThetaPaper*paperQAbsLog nonnegativity remains. -/
theorem S3044_hscalar_of_CTheta_nonneg
    (logQ : Real) (a b c : Nat)
    (hC : 0 <= CThetaPaper fiveLabel logQ 0 S2990ActualDFpdActual.S2990DFpd
      (S2990ActualDFpdActual.S2990FFpd a b c) 0 0 *
        paperQAbsLog fiveLabel logQ) :
    S3034Hscalar R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat D logQ a b c := by
  unfold S3034Hscalar S3025MissingThetaUpperScalar
  have hV := S3043_logVolume_nonneg
    (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat D)
  have hneg : - actualC3LogShellTensorLogVolume
      (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat D) <= 0 := by linarith
  exact le_trans hneg hC


/-- Conditional route to V >= 0: it suffices that the actual tensor region has
Haar measure at least 1.  The compactness of the region gives finiteness. -/
theorem S3044_V_nonneg_of_region_measure_ge_one
    (hregion : (1 : ENNReal) <=
      actualC3LogShellTensorHaar
        (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat
          horbCompat secCompat hsecCompat cusCompat hcusCompat D)
        (actualC3LogShellTensorRegion
          (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat
            horbCompat secCompat hsecCompat cusCompat hcusCompat D))) :
    0 <= actualC3LogShellTensorLogVolume
      (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat D) := by
  unfold actualC3LogShellTensorLogVolume
  have hlt : actualC3LogShellTensorHaar
        (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat
          horbCompat secCompat hsecCompat cusCompat hcusCompat D)
        (actualC3LogShellTensorRegion
          (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat
            horbCompat secCompat hsecCompat cusCompat hcusCompat D)) < ⊤ :=
    (actualC3LogShellTensorRegion_compact
      (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat D)).measure_lt_top
  have hto : (1 : Real) <=
      ((actualC3LogShellTensorHaar
        (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat
          horbCompat secCompat hsecCompat cusCompat hcusCompat D))
        (actualC3LogShellTensorRegion
          (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat
            horbCompat secCompat hsecCompat cusCompat hcusCompat D))).toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono (ne_top_of_lt hlt) hregion
  simpa using hto


/-- Special case logQ = 0: hscalar reduces to V >= 0. -/
theorem S3044_hscalar_zero_logQ
    (a b c : Nat)
    (hV : 0 <= actualC3LogShellTensorLogVolume
      (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat D)) :
    S3034Hscalar R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat D 0 a b c := by
  unfold S3034Hscalar S3025MissingThetaUpperScalar
  simp only [paperQAbsLog, qNormFactor, zero_mul, mul_zero]
  linarith

/-- Exact missing sign: the actual C3 tensor log-volume is nonnegative. -/
def S3044MissingVNonneg : Prop :=
  0 <= actualC3LogShellTensorLogVolume
    (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat D)

#check S3044_hscalar_of_nonneg
#check S3044_hscalar_zero_logQ
#check S3044_hscalar_of_CTheta_nonneg
#check S3044_V_nonneg_of_region_measure_ge_one
#check S3044MissingVNonneg

end LeanFormal.IUT.XiFPaper.S3044HscalarBySignActual
end