import tmp.sheaf.xif.paper.S3078HullNativeMagnitudeProducerActual
import tmp.sheaf.xif.paper.S3070HullNativeMagnitudeBoundAttempt

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3078HullNativeMagnitudeProducerActual
open LeanFormal.IUT.XiFPaper.S3070HullNativeMagnitudeBoundAttempt
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullSumActual
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotHullLogVolumeActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3079GlobalSumIdentificationAttempt

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv} [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : forall v : V, I.SourceImageRealization v)
variable (n : ThetaPilotCarrier l)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The exact index map needed: source places V are the native bad places. -/
def S3079IndexMap (V : Type uv) : Type (max uv) :=
  V ≃ Bad (nativePlaceSelection T)

/-- Per-place identification of the source hull log at v with the native local
theta-hull formula at the mapped bad place. -/
def S3079PerPlaceIdentification (e : S3079IndexMap T V) : Prop :=
  forall v : V,
    Real.log (I.sourceSetVolume v (I.sourceHolomorphicHull v (R v) n)).toReal =
      localThetaHullLogFormula T (e.toFun v)

/-- Exact target of S3079. -/
def S3079GlobalSumIdentification : Prop :=
  globalThetaHullLogVolume (I := I) R n =
    ∑ b : Bad (nativePlaceSelection T), localThetaHullLogFormula T b

#check S3079IndexMap
#check S3079PerPlaceIdentification
#check S3079GlobalSumIdentification

end LeanFormal.IUT.XiFPaper.S3079GlobalSumIdentificationAttempt
end