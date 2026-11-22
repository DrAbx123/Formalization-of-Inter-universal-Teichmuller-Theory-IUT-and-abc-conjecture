import tmp.sheaf.xif.paper.S3134MainlineRootedHFaActual
import tmp.sheaf.xif.paper.S1300HDDHullDetActual
import tmp.sheaf.xif.paper.S3134FourthTriangleCompositionStatusActual
import tmp.sheaf.xif.paper.S3134Step3115To312Actual
import tmp.sheaf.xif.paper.S3132R1ThetaHalfBridgeActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3134MainlineRootedHFaActual
open LeanFormal.IUT.XiFPaper.S3134Step3115To312Actual
open LeanFormal.IUT.XiFPaper.S3134FourthJointQThetaActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3132R1ThetaHalfBridgeActual
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.S3132CanonicalRootedThetaTargetActual

universe u v uv upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]
variable {V0 : Type} {I0 : OriginalInput l V0}
variable (C3 : SourcePilotRegionData (l := l) (V := V0) I0)

/-!
# task-41(a) sharper target: canonical rooted V-form Theta readout

**Component, not a paper object.**  Owner: hull.  Consumer: the normalization
residual `MissingThetaLogNormalization` of task-38 (and shehdd's wiring
`S3134Step3115_canonicalQC_le_thetaPilot`).

shehdd's corrected convention: the paper-faithful Theta readout is the signed
degree-normalized V-form rooted sum `S3134CanonicalRootedHC T mu` (mainline
`S3131CanonicalRootedHC` rebuilt in `S3134MainlineRootedHFaActual`; IUT III,
Proposition 3.9, (i), p. 115; Corollary 3.12, corpus lines 10324-10353).  The
sharper target recorded here is

    thetaPilotHullLogVolumeReal C3 = S3134CanonicalRootedHC T mu,

with the remaining Θ-side identification
`S3134CanonicalRootedHC T mu = S3134Step3115ThetaPilotReadout D` kept as an
explicit hypothesis (shehdd's named residual; consumer
`S3134Step3115_canonicalQC_le_thetaPilot`).  The transport residual
`MissingC3PacketUniformComparison` is NOT needed for this step: normalization
and carrier transport are independent residuals (task-38 reduction).
-/

/-- **Sharper paper-faithful target (exact missing, owner hull).**  The actual C3
packet Theta reading equals the canonical rooted V-form readout. -/
structure MissingCanonicalRootedThetaReadout
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (I : Input Label Choice)
    {l : PrimeGeFive} {V0 : Type} {I0 : OriginalInput l V0}
    (C3 : SourcePilotRegionData (l := l) (V := V0) I0)
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
    [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)] : Prop where
  theta_eq_canonical :
    thetaPilotHullLogVolumeReal C3 = S3134CanonicalRootedHC T mu

/-- **Composition:** the sharper target plus shehdd's Θ-side identification gives
the task-30 Theta-half readout equality (raw readout convention). -/
theorem S3134Step3115ThetaPilotReadout_eq_thetaPilot_of_canonical
    (D : S1300HDDHullDetSource I)
    (hC : MissingCanonicalRootedThetaReadout I C3 T mu)
    (hH : S3134CanonicalRootedHC T mu =
      S3134Step3115ThetaPilotReadout (I := I) D) :
    S3134Step3115ThetaPilotReadout (I := I) D = thetaPilotHullLogVolumeReal C3 := by
  rw [← hH, hC.theta_eq_canonical]

#check MissingCanonicalRootedThetaReadout
#check S3134Step3115ThetaPilotReadout_eq_thetaPilot_of_canonical

end LeanFormal.IUT.XiFPaper.S3132CanonicalRootedThetaTargetActual

end
