import tmp.sheaf.xif.paper.S3068GlobalReadoutLeActual
import tmp.sheaf.xif.paper.GlobalQVFamThetaHullSumActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotHullLogVolumeActual
open LeanFormal.IUT.XiFPaper.S1675GlobalReadoutNormalizationActual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3068GlobalReadoutLeActual
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullSumActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3070HullNativeMagnitudeBoundAttempt

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv} [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : forall v : V, I.SourceImageRealization v)
variable (n : ThetaPilotCarrier l)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

def S3070HullNativeMagnitudeBound : Prop :=
  S1675HullNativeMagnitudeBound (I := I) R n T

theorem S3070_hullLog_eq_sum :
    globalThetaHullLogVolume (I := I) R n =
      ∑ v : V, Real.log
        (I.sourceSetVolume v (I.sourceHolomorphicHull v (R v) n)).toReal :=
  globalThetaHullLogVolume_eq (I := I) R n

/-- Conditional global readout from the exact missing hull/native bound. -/
theorem S3070_globalReadout_of_bound
    (hnorm : S1675OneColumnNormalization (I := I) T)
    (hbound : S3070HullNativeMagnitudeBound (I := I) R n T) :
    S3068GlobalReadoutLe (I := I) R n := by
  unfold S3070HullNativeMagnitudeBound at hbound
  exact S3068GlobalReadoutLe_of_native (I := I) R n T hnorm hbound

def S3070LocalFormulaGap (b : Bad (nativePlaceSelection T)) : Type :=
  GlobalQVFamThetaHullSumActual.LocalThetaHullFormulaGap T b

#check S3070HullNativeMagnitudeBound
#check S3070_hullLog_eq_sum
#check S3070_globalReadout_of_bound
#check S3070LocalFormulaGap
#print axioms S3070_globalReadout_of_bound

end LeanFormal.IUT.XiFPaper.S3070HullNativeMagnitudeBoundAttempt
end
