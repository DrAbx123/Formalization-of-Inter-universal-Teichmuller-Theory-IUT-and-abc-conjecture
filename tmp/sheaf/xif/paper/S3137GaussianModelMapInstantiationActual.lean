import tmp.sheaf.xif.paper.S3133S3131GaussianModelComponentsActual
import tmp.sheaf.xif.paper.S3137SameCModelMapResidualActual
import tmp.sheaf.xif.paper.S3131Stage2ModelMapActual
import LeanFormal.IUT.Audit.Status

/-!
# S3137: Gaussian-model instantiation of the same-C model-map residual

Lead item (2): instantiate SameCModelMapResidual from qpilot's Gaussian model
components (S3133S3131GaussianModelComponentsActual) plus canonical readouts,
proving as many M-fields as actual theorems and leaving only genuine missing.

Proved here from actual theorems:
* M0 (T.arithmetic = I.initial.arithmetic): from qpilot's Gaussian arithmetic
  matches and bridge S3133GaussianArithmeticMatch_bridge (IUT I Def 3.1);
* M2 reduction: from qpilot's S3131BadTensorPrimeMatch_of_basePlace (actual
  prime comparison qVFamTensorP_eq_base_val + base-place equality);
* M3 reduction for the actual Gaussian Stage-2 image: its actual theta packet
  has q = 1/5 (qpilot S3133GaussianStage2ThetaPacket_q), so M3 becomes the
  explicit order-one q-norm equality ||C3.q|| = 1/5 (the Gaussian q parameter
  is (1/5)^order, IUT I Ex 3.2(iv)); the q-norm equality is a genuine residual.

Still supplied as named hypotheses (not asserted, not derivable here):
* M1 source placeToMod provenance (contract-separated in the tree);
* M3 order-one q-norm equality above;
* M4 raw weight total-one (variant B; normalized-weight alternative exists);
* M5a/M5b canonical readout equalities (mainline/qpilot/shehdd task-40).

From these the residual SameCModelMapResidual and the signed/magnitude Cor
3.12 comparisons follow via S3137SameCModelMapResidualActual.  No carrier
substitution, no sorry, no axiom.  WRITE-ONLY.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137GaussianModelMapInstantiationActual

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
open LeanFormal.IUT.XiFPaper.S3133S3131PlaceIndexComparisonActual
open LeanFormal.IUT.XiFPaper.S3133S3131GaussianModelComponentsActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3137SameCModelMapResidualActual
open LeanFormal.IUT.XiFPaper.S3131Stage2ModelMapActual
open LeanFormal.IUT.XiFPaper.C3GaussianThetaPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open MeasureTheory
open scoped BigOperators

variable {l : PrimeGeFive} {V : Type}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [forall b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [forall b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]
variable (mu : forall b : Bad (nativePlaceSelection T),
  Measure (qVFamTensorBlock T b))
variable [forall b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- **M0 proved from qpilot's Gaussian arithmetic matches** (IUT I Def 3.1): if
the native T and the Stage-2 initial data both carry the concrete Gaussian
arithmetic, they carry the same arithmetic input. -/
theorem gaussian_M0 (hT : S3133GaussianModelArithmeticMatch T)
    (hS : S3133GaussianStage2ArithmeticMatch I.initial) :
    T.arithmetic = I.initial.arithmetic :=
  S3133GaussianArithmeticMatch_bridge T I.initial hT hS

/-- **M2 reduced to the base-place equality** using qpilot's actual prime
comparison (qVFamTensorP_eq_base_val). -/
theorem gaussian_M2_of_basePlace
    (hbase : forall b : Bad (nativePlaceSelection T),
      (completionRationalPrime b.1).val = C3.p) :
    S3131BadTensorPrimeMatch (l := l) T C3 :=
  S3131BadTensorPrimeMatch_of_basePlace T C3 hbase

/-- **M3 for the actual Gaussian Stage-2 image reduces to the order-one q-norm
equality.**  The actual Gaussian Stage-2 theta packet has q = 1/5 (qpilot), so
the M3 packet identification becomes ||C3.q|| = 1/5, i.e. the Gaussian q
parameter has order one. -/
theorem gaussian_M3_of_orderOneQNorm
    (D : SourcePilotRegionDonors (I := I))
    (h : ‖(actualGaussianC3 (l := l) (V := V) (I := I) D).q.q‖ = ((5 : Real)⁻¹)) :
    (actualGaussianC3 (l := l) (V := V) (I := I) D).thetaPacket.q =
      ‖(actualGaussianC3 (l := l) (V := V) (I := I) D).q.q‖ :=
  (S3133GaussianStage2ThetaPacket_q (l := l) (V := V) (I := I) D).trans h.symm

/-- **Assembly: SameCModelMapResidual from the Gaussian model, with M0 proved
and M2/M3 reduced; M1, the order-one q-norm equality, M4 and the two readout
equalities remain the supplied residual hypotheses.** -/
theorem sameCModelMapResidual_of_gaussianModel
    (hT : S3133GaussianModelArithmeticMatch T)
    (hS : S3133GaussianStage2ArithmeticMatch I.initial)
    (hM1 : S3131BadTensorIndexEquivalence (l := l) T C3)
    (hbase : forall b : Bad (nativePlaceSelection T),
      (completionRationalPrime b.1).val = C3.p)
    (hM3 : C3.thetaPacket.q = ‖C3.q.q‖)
    (hM4 : (∑ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b) = 1)
    (hM5a : forall b : Bad (nativePlaceSelection T),
      S3131PaperQReadout (l := l) T mu b = qPilotLogVolumeReading P)
    (hM5b : forall b : Bad (nativePlaceSelection T),
      S3131PaperHullReadout (l := l) T mu b = thetaPilotHullLogVolumeReal C3) :
    SameCModelMapResidual (l := l) T mu C3 P :=
  ⟨gaussian_M0 (l := l) (T := T) (I := I) hT hS, hM1,
    gaussian_M2_of_basePlace (l := l) (T := T) (C3 := C3) hbase,
    hM3, hM4, hM5a, hM5b⟩

/-- **Cor 3.12 comparison from the Gaussian model-map instantiation.** -/
theorem qThetaPilotLogVolumeComparison_of_gaussianModel
    (M : SameCModelMapResidual (l := l) T mu C3 P) :
    qThetaPilotLogVolumeComparison C3 P :=
  qThetaPilotLogVolumeComparison_of_modelMap (l := l) T mu C3 P M

end LeanFormal.IUT.XiFPaper.S3137GaussianModelMapInstantiationActual

namespace LeanFormal.IUT.Audit

/-- **Gaussian-model M-field delta.**  Proved from actual theorems: M0 (qpilot
Gaussian arithmetic matches + bridge, IUT I Def 3.1); M2 reduced to the actual
base-prime equality (qpilot qVFamTensorP_eq_base_val); M3 reduced for the actual
Gaussian Stage-2 image to the order-one q-norm equality ||C3.q|| = 1/5 (qpilot
actual Gaussian packet q = 1/5).  Remaining residual: M1 source placeToMod
provenance (contract-separated), the M3 order-one q-norm equality, M4 variant-B
raw weight total-one (normalized alternative exists), and M5a/M5b canonical
readout equalities (task-40). -/
def s3137GaussianModelMapDelta : Obligation :=
  { id := "S3137.residual.R1-gaussian-model-map-delta"
    source := "IUT I, Def 3.1, Ex. 3.2(iv); IUT II, Remark 2.5.1, (i); IUT III, Prop. 3.4, (ii), pp. 102-103; Def. 3.8, (i), p. 112; Remark 3.1.1, (ii); IUT IV, Prop. 1.4, (i); Cor. 3.12"
    status := VerificationStatus.pending
    note := "M0 proved (qpilot Gaussian arithmetic bridge); M2 reduced to base-prime equality (qpilot qVFamTensorP_eq_base_val); M3 reduced to order-one q-norm equality for actualGaussianC3 (packet q=1/5 actual).  Remaining: M1 placeToMod provenance, M3 order-one equality, M4 variant-B, M5a/M5b readout equalities.  No assertion; consumer derives Cor 3.12 comparison from the residual."
    dependsOn := ["S3133S3131GaussianModelComponentsActual", "S3137SameCModelMapResidualActual", "S3131Stage2ModelMapActual"] }

end LeanFormal.IUT.Audit