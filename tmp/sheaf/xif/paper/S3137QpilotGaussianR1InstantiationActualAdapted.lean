import tmp.sheaf.xif.paper.S3133S3131GaussianModelMapMinimalActual
import tmp.sheaf.xif.paper.S3137QThetaComparisonBridgeActual
import LeanFormal.IUT.Audit.Status

/-!
# S3137: instantiate the R1 residual from qpilot's minimal Gaussian model map

Lead task: consume qpilot's S3133GaussianModelMapMinimalActual interface and
instantiate the R1 same-C residual so that as many M-fields as possible are
actual theorems, leaving only genuine missing fields.

qpilot's minimal residual supplies:
* R.C : SourceCompletion.{0} l with arithmetic_eq to the concrete Gaussian
  arithmetic (M0 supply);
* M1 exact residual: R.m1_indexInjection : Prop (bad <-> all-place index
  injection; genuine source placeToMod provenance missing);
* shrunk M2 residual: R.m2_baseQMatch : Prop (= S3133GaussianQParameterMatchAtBase
  T: clause-B q has norm 1/5 at bad places above 5);
and PROVES M0 (S3133GaussianModelMapResidualMinimal_m0) and M3
(S3133GaussianModelMapResidualMinimal_m3: actual Gaussian Stage-2 image theta
values match the actual source theater).

This file:
* re-exports the PROVED M0 and M3 for T := R.C.toSourceNativeInitialThetaData
  and C3 := actualGaussianC3 D;
* records the reduced R1 residual as exactly {M1, M2} (both Props of qpilot's
  record) plus the readout-side residual {M4 weight total, M5a/M5b canonical
  readout equalities} that mainline/qpilot/shehdd are assembling;
* proves the same-C bridge from M4+M5a/M5b and hence the signed Cor 3.12
  comparison and magnitude form (via mainline's unconditional paper-normalized
  same-coefficient comparison).

No carrier substitution, no sorry, no axiom.  WRITE-ONLY.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137QpilotGaussianR1InstantiationActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3131QCLeHCComparisonActual
open LeanFormal.IUT.XiFPaper.S3131PaperNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.S3131SameCSourceInputActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.C3GaussianThetaPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3133S3131GaussianModelComponentsActual
open LeanFormal.IUT.XiFPaper.S3133S3131GaussianModelMapMinimalActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3137QThetaComparisonBridgeActual
open LeanFormal.IUT.XiFPaper.S3137NativeToC3SameCReadoutActual
open MeasureTheory
open scoped BigOperators

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (D : SourcePilotRegionDonors (I := I))
variable (R : S3133GaussianModelMapResidualMinimal (l := l) (I := I) D)

/-- The native datum of qpilot's minimal residual. -/
abbrev gaussianT : SourceNativeInitialThetaData.{0} l :=
  R.C.toSourceNativeInitialThetaData

/-- The actual Gaussian Stage-2 image. -/
abbrev gaussianC3 : SourcePilotRegionData (l := l) (V := V) I :=
  actualGaussianC3 (l := l) (V := V) (I := I) D

variable [Fintype (Bad (nativePlaceSelection gaussianT))]
variable [forall b : Bad (nativePlaceSelection gaussianT),
  MeasurableSpace (qVFamTensorBlock gaussianT b)]
variable [forall b : Bad (nativePlaceSelection gaussianT),
  BorelSpace (qVFamTensorBlock gaussianT b)]
variable (mu : forall b : Bad (nativePlaceSelection gaussianT),
  Measure (qVFamTensorBlock gaussianT b))
variable [forall b : Bad (nativePlaceSelection gaussianT), Measure.IsAddHaarMeasure (mu b)]
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- **M0 PROVED** from qpilot's minimal residual (actual SourceCompletion above
the model arithmetic, IUT I Def 3.1). -/
theorem gaussianR1_M0_proved :
    S3133GaussianModelArithmeticMatch (l := l) gaussianT :=
  S3133GaussianModelMapResidualMinimal_m0 (l := l) (V := V) (I := I) D R

/-- **M3 PROVED** for the actual Gaussian Stage-2 image (IUT II Remark 2.5.1(i)). -/
theorem gaussianR1_M3_proved :
    S3133GaussianThetaValueMatch (l := l) (V := V) (I := I) gaussianC3 :=
  S3133GaussianModelMapResidualMinimal_m3 (l := l) (V := V) (I := I) D

/-- The weighted q-side collapse for the Gaussian model (M4+M5a). -/
theorem gaussianR1_regionalQ_eq
    (hM4 : (∑ b : Bad (nativePlaceSelection gaussianT),
        nativeBadLocalWeight gaussianT b) = 1)
    (hM5a : forall b : Bad (nativePlaceSelection gaussianT),
      S3131PaperQReadout (l := l) gaussianT mu b = qPilotLogVolumeReading P) :
    S3131PaperRegionalQ (l := l) gaussianT mu = qPilotLogVolumeReading P := by
  unfold S3131PaperRegionalQ
  rw [Finset.sum_congr rfl (fun b _ => by rw [hM5a b])]
  rw [← Finset.sum_mul, hM4, one_mul]

/-- The weighted Theta-hull collapse for the Gaussian model (M4+M5b). -/
theorem gaussianR1_regionalHull_eq
    (hM4 : (∑ b : Bad (nativePlaceSelection gaussianT),
        nativeBadLocalWeight gaussianT b) = 1)
    (hM5b : forall b : Bad (nativePlaceSelection gaussianT),
      S3131PaperHullReadout (l := l) gaussianT mu b = thetaPilotHullLogVolumeReal gaussianC3) :
    S3131PaperRegionalHull (l := l) gaussianT mu = thetaPilotHullLogVolumeReal gaussianC3 := by
  unfold S3131PaperRegionalHull
  rw [Finset.sum_congr rfl (fun b _ => by rw [hM5b b])]
  rw [← Finset.sum_mul, hM4, one_mul]

/-- **Same-C bridge for the Gaussian model from M4+M5a/M5b.** -/
theorem gaussianR1_bridge
    (hM4 : (∑ b : Bad (nativePlaceSelection gaussianT),
        nativeBadLocalWeight gaussianT b) = 1)
    (hM5a : forall b : Bad (nativePlaceSelection gaussianT),
      S3131PaperQReadout (l := l) gaussianT mu b = qPilotLogVolumeReading P)
    (hM5b : forall b : Bad (nativePlaceSelection gaussianT),
      S3131PaperHullReadout (l := l) gaussianT mu b = thetaPilotHullLogVolumeReal gaussianC3) :
    SameCQThetaReadoutBridge (l := l) gaussianT mu gaussianC3 P := by
  refine ⟨?_, ?_⟩
  · exact (gaussianR1_regionalQ_eq (l := l) (I := I) D R mu P hM4 hM5a).symm
  · exact (gaussianR1_regionalHull_eq (l := l) (I := I) D R mu P hM4 hM5b).symm

/-- **Cor 3.12 signed comparison for the Gaussian model**, from the reduced
residual M1+M2 (qpilot) and the readout residual M4+M5a/M5b. -/
theorem qThetaPilotLogVolumeComparison_of_qpilotMinimal
    (hM4 : (∑ b : Bad (nativePlaceSelection gaussianT),
        nativeBadLocalWeight gaussianT b) = 1)
    (hM5a : forall b : Bad (nativePlaceSelection gaussianT),
      S3131PaperQReadout (l := l) gaussianT mu b = qPilotLogVolumeReading P)
    (hM5b : forall b : Bad (nativePlaceSelection gaussianT),
      S3131PaperHullReadout (l := l) gaussianT mu b = thetaPilotHullLogVolumeReal gaussianC3) :
    qThetaPilotLogVolumeComparison gaussianC3 P :=
  qThetaPilotLogVolumeComparison_of_sameC (l := l) gaussianT mu gaussianC3 P
    (gaussianR1_bridge (l := l) (I := I) D R mu P hM4 hM5a hM5b)

end LeanFormal.IUT.XiFPaper.S3137QpilotGaussianR1InstantiationActualAdapted

namespace LeanFormal.IUT.Audit

/-- **Reduced R1 residual after qpilot's minimal Gaussian model map.**
Proved from actual theorems: M0 (actual SourceCompletion with model arithmetic)
and M3 (actual Gaussian Stage-2 theta values match the source theater).
Remaining residual: M1 (genuine source placeToMod provenance, bad<->all-place
injection; contract-separated), shrunk M2 (clause-B base-q descent + Gaussian
norm 1/5 at bad places above 5), M4 raw weight total-one (normalized variant
exists), and M5a/M5b canonical readout equalities.  The signed comparison and
magnitude form follow from the readout part via mainline's unconditional
paper-normalized comparison. -/
def s3137QpilotGaussianR1Reduced : Obligation :=
  { id := "S3137.residual.R1-reduced-qpilot-gaussian"
    source := "IUT I, Def 3.1, Ex. 3.2(iv); IUT II, Remark 2.5.1, (i); IUT III, Prop. 3.4, (ii), pp. 102-103; Def. 3.8, (i), p. 112; Remark 3.1.1, (ii); IUT IV, Prop. 1.4, (i); Cor. 3.12"
    status := VerificationStatus.pending
    note := "M0 and M3 proved via qpilot S3133GaussianModelMapMinimalActual; reduced residual = M1 (source placeToMod provenance) + shrunk M2 (clause-B base-q descent/Gaussian norm) + M4 raw weight total-one + M5a/M5b readout equalities.  Comparison derived from readout part.  No proof of residual fields assumed."
    dependsOn := ["S3133S3131GaussianModelMapMinimalActual", "S3137QThetaComparisonBridgeActual", "S3137QpilotGaussianR1InstantiationActualAdapted"] }

end LeanFormal.IUT.Audit
