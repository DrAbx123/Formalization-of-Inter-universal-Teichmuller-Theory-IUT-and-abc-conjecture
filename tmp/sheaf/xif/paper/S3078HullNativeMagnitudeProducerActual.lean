import tmp.sheaf.xif.paper.S3070HullNativeMagnitudeBoundAttempt
import tmp.sheaf.xif.paper.GlobalQVFamThetaHullSumActual
import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.LocalPerBHullNormalizedLogActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import tmp.sheaf.xif.paper.QVPilotThetaHullNestingActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullSumActual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S1675GlobalReadoutNormalizationActual
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotHullLogVolumeActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.LocalPerBHullNormalizedLogActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.QVPilotThetaHullNestingActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3078HullNativeMagnitudeProducerActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv} [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : forall v : V, I.SourceImageRealization v)
variable (n : ThetaPilotCarrier l)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Per-place actual inequality: the local theta-hull formula log is
nonpositive, while the native weighted q-pilot magnitude is nonnegative. -/
theorem S3078_localFormula_le_native_weight
    (b : Bad (nativePlaceSelection T)) :
    localThetaHullLogFormula T b <=
      nativeBadLocalWeight T b * baseQLogMagnitude T b := by
  have hp1 : (1 : Real) < (qVFamilyResiduePrime T b : Real) := by
    unfold qVFamilyResiduePrime
    exact_mod_cast (NumberFieldFinitePlace.residueCharacteristic_prime b.1).one_lt
  have hlogp : 0 < Real.log (qVFamilyResiduePrime T b : Real) :=
    Real.log_pos hp1
  have hcoef : 0 <= GlobalQVFamThetaHullSumActual.qVFamilyLatticeCoefficient T b := by
    unfold GlobalQVFamThetaHullSumActual.qVFamilyLatticeCoefficient
      GlobalQVFamThetaHullSumActual.qVFamilyBasePLogCoefficient
    apply mul_nonneg (Nat.cast_nonneg _)
    apply div_nonneg
    · exact Real.log_nonneg (le_of_lt (residueNormBase_gt_one ((nativeBadLift T).lift b)))
    · exact le_of_lt hlogp
  have hprod : 0 <= GlobalQVFamThetaHullSumActual.qVFamilyLatticeCoefficient T b *
      Real.log (qVFamilyResiduePrime T b : Real) := mul_nonneg hcoef (le_of_lt hlogp)
  have hleft : localThetaHullLogFormula T b <= 0 := by
    unfold localThetaHullLogFormula
    nlinarith
  have hweight : 0 <= nativeBadLocalWeight T b := by
    rw [nativeBadLocalWeight_eq_inv]
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  have hright : 0 <= nativeBadLocalWeight T b * baseQLogMagnitude T b :=
    mul_nonneg hweight (le_of_lt (baseQLogMagnitude_pos T b))
  linarith

/-- Conditional global bound: if the actual global theta hull log-volume is the
weighted sum of the local formulas, the S3070/S1675 bound follows. -/
theorem S3078_hullNativeMagnitudeBound_of_sum
    (hsum : globalThetaHullLogVolume (I := I) R n =
      ∑ b : Bad (nativePlaceSelection T), localThetaHullLogFormula T b) :
    S1675HullNativeMagnitudeBound (I := I) R n T := by
  unfold S1675HullNativeMagnitudeBound
  rw [hsum]
  rw [nativeGlobalQPilotNormalizedLogMagnitude_eq]
  apply Finset.sum_le_sum
  intro b _
  exact S3078_localFormula_le_native_weight (l := l) T b

/-- Exact first missing global identity: the source per-place hull sum equals
the native bad-place sum of local theta-hull formulas. -/
def S3078GlobalSumIdentification : Prop :=
  globalThetaHullLogVolume (I := I) R n =
    ∑ b : Bad (nativePlaceSelection T), localThetaHullLogFormula T b

#check S3078_localFormula_le_native_weight
#check S3078_hullNativeMagnitudeBound_of_sum
#check S3078GlobalSumIdentification

end LeanFormal.IUT.XiFPaper.S3078HullNativeMagnitudeProducerActual
end