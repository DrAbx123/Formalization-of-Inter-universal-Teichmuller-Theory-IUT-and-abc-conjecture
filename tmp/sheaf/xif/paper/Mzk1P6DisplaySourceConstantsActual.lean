/- P6 display source constants: actual P6DisplaySourceData inhabitant with
dFpd = S2990DFpd, fFpd = S2990FFpd a b c, etaPrm from the realized ExpEst02
prime-reciprocal-sum estimate, dmod = lgpDStarMod 1, eStar = lgpEStarMod 1,
and logQ = -log (qVFamNormalizedNorm).  No chosen 0/1 placeholders. -/
import tmp.sheaf.xif.paper.Mzk1P6DisplayDictionaryActual
import tmp.sheaf.xif.paper.S3136IVThm110ConstantsActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import tmp.sheaf.xif.paper.S2990ActualDFpdActual
import tmp.sheaf.xif.paper.S2945CertificateActual
import tmp.sheaf.xif.paper.Mzk1ExpEst02RealizedActual
import tmp.sheaf.xif.paper.S2752FinalHweightvolActual
import tmp.sheaf.xif.paper.S2771Gap1ClosedActual
import Mathlib.Tactic

set_option maxHeartbeats 4000000
noncomputable section
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.Mzk1P6DisplayDictionaryActual
open LeanFormal.IUT.XiFPaper.S3136IVThm110ConstantsActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.S2990ActualDFpdActual
open LeanFormal.IUT.XiFPaper.S2945CertificateActual
open LeanFormal.IUT.XiFPaper.Mzk1ExpEst02RealizedActual
open LeanFormal.IUT.XiFPaper.ExpEst02ElementaryEstimatesActual
open LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual

namespace LeanFormal.IUT.XiFPaper.Mzk1P6DisplaySourceConstantsActual

/-- Concrete prime l = 7. -/
def p6LSeven : PrimeGeFive where
  value := 7
  prime := by norm_num
  ge_five := by norm_num

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))

/-- Actual P6 display source data from actual constants: dFpd/fFpd from the
S2990 model constants, etaPrm from the realized ExpEst02 estimate, dmod/eStar
from the S3136 constant formulas, and logQ from the actual qHat normalized norm. -/
noncomputable def p6DisplaySourceDataConstants : P6DisplaySourceData where
  l := p6LSeven
  l_ge_seven := by
    norm_num [p6LSeven]
  dmod := lgpDStarMod 1
  dmod_ge_one := by
    unfold lgpDStarMod
    norm_num
  dFpd := S2990DFpd
  fFpd := S2990FFpd 1 1 1
  dFpd_ge_one := by
    have hne : differentIdeal ℤ S2990R ≠ 0 := differentIdeal_ne_bot
    have hpos : 0 < Ideal.absNorm (differentIdeal ℤ S2990R) := by
      rw [Ideal.absNorm_pos_iff_mem_nonZeroDivisors]
      exact mem_nonZeroDivisors_iff_ne_zero.mpr hne
    have hnat : (1 : Nat) ≤ Ideal.absNorm (differentIdeal ℤ S2990R) :=
      Nat.succ_le_of_lt hpos
    unfold S2990DFpd
    exact_mod_cast hnat
  fFpd_ge_one := by
    have hne : S2752J S2771FiveLabel 1 1 1 ≠ 0 :=
      S2945_supportIdeal_ne_bot 1 1 1
    have hpos : 0 < Ideal.absNorm (S2752J S2771FiveLabel 1 1 1) := by
      rw [Ideal.absNorm_pos_iff_mem_nonZeroDivisors]
      exact mem_nonZeroDivisors_iff_ne_zero.mpr hne
    have hnat : (1 : Nat) ≤ Ideal.absNorm (S2752J S2771FiveLabel 1 1 1) :=
      Nat.succ_le_of_lt hpos
    unfold S2990FFpd
    exact_mod_cast hnat
  eStar := (lgpEStarMod 1 : Real)
  etaPrm := Classical.choose expEstPrimeReciprocalSum_realized
  logQ := -Real.log (qVFamNormalizedNorm T b)
  logQ_pos := by
    have hpos : 0 < qVFamNormalizedNorm T b :=
      norm_pos_iff.mpr (qVFamNormalizedGenerator_ne_zero T b)
    have hlt : qVFamNormalizedNorm T b < 1 := by
      rw [qVFamNormalizedNorm]
      exact qVFamNormalizedGenerator_norm_lt_one T b
    exact neg_pos.mpr (Real.log_neg hpos hlt)
  eta_nonneg := by
    have heta : 0 < Classical.choose expEstPrimeReciprocalSum_realized :=
      (Classical.choose_spec expEstPrimeReciprocalSum_realized).1
    positivity

@[simp] theorem p6DisplaySourceDataConstants_logQ :
    (p6DisplaySourceDataConstants T b).logQ =
      -Real.log (qVFamNormalizedNorm T b) := rfl

@[simp] theorem p6DisplaySourceDataConstants_dmod :
    (p6DisplaySourceDataConstants T b).dmod = lgpDStarMod 1 := rfl

#print axioms p6DisplaySourceDataConstants

end LeanFormal.IUT.XiFPaper.Mzk1P6DisplaySourceConstantsActual
end
