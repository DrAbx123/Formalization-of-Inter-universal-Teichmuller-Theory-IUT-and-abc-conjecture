import tmp.sheaf.xif.paper.S3137NativeToC3SameCReadoutActual
import tmp.sheaf.xif.paper.S3131PaperNormalizedComparisonActual
import tmp.sheaf.xif.paper.S3133S3131PlaceIndexComparisonActual
import LeanFormal.IUT.Audit.Status

/-!
# S3137: same-C model-map residual and consumer (R1, final M-list)

Lead/mainline R1 reassignment: the same-C model-map residual is defined and
consumed here, in the S3137 working variable block, using mainline's FINAL
M-list:

* M0 native T <-> OriginalInput (same initial Theta-data): IUT I, Def 3.1;
* M1 Bad <-> C3.tensorIndex: qpilot S3131BadTensorIndexEquivalence
  (IUT I, Def 3.1, (b), (e); IUT III, Prop. 3.4, (ii), pp. 102-103);
* M2 qVFamily q <-> C3 q parameters (prime-level): qpilot
  S3131BadTensorPrimeMatch (IUT I, Ex. 3.2, (iv); IUT III, Def. 3.8, (i),
  p. 112);
* M3 theta values <-> C3.thetaPacket: the packet q is the actual source q
  norm (IUT II, Remark 2.5.1, (i): theta values are q_v^{j^2});
* M4 (variant B) the raw Remark 3.1.1(ii) weight sum is one
  (nativeBadLocalWeight total; qpilot S3131WeightSumOneHypothesis is the same
  component);
* M5a/M5b the per-place readout equalities: the paper-normalized q / Theta-hull
  readouts equal the Stage-2 readings (IUT IV, Prop. 1.4, (i); IUT III, Prop.
  3.9, (i), p. 115; Cor. 3.12).

The collapse from M4+M5a/M5b to the two global same-C readout equalities is
PROVED here; M0-M3 are the cross-carrier object matches that make the M-list
paper-faithful and are kept as residual hypotheses (not derivable, not
asserted).  Consumer: qThetaPilotLogVolumeComparison C3 P (signed Cor 3.12
comparison) and its magnitude form, both via mainline's unconditional
paper-normalized comparison.  No carrier substitution, no sorry, no axiom.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137SameCModelMapResidualActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3131QCLeHCComparisonActual
open LeanFormal.IUT.XiFPaper.S3131PaperNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.S3131SameCSourceInputActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S3133S3131PlaceIndexComparisonActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3137NativeToC3SameCReadoutActual
open LeanFormal.IUT.XiFPaper.S3137QThetaComparisonBridgeActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open MeasureTheory
open scoped BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [forall b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [forall b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]
variable (mu : forall b : Bad (nativePlaceSelection T),
  Measure (qVFamTensorBlock T b))
variable [forall b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- **The same-C model-map residual (final M-list).**  M0-M3 are the cross-carrier
object matches of the paper's initial Theta-data/theta-value dictionary; M4 is
the variant-B raw weight total-one; M5a/M5b are the readout equalities whose
weighted collapse yields the two global same-C readout equalities. -/
def SameCModelMapResidual : Prop :=
  (T.arithmetic = I.initial.arithmetic) ∧
    S3131BadTensorIndexEquivalence (l := l) T C3 ∧
    S3131BadTensorPrimeMatch (l := l) T C3 ∧
    (C3.thetaPacket.q = ‖C3.q.q‖) ∧
    ((∑ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b) = 1) ∧
    (forall b : Bad (nativePlaceSelection T),
      S3131PaperQReadout (l := l) T mu b = qPilotLogVolumeReading P) ∧
    (forall b : Bad (nativePlaceSelection T),
      S3131PaperHullReadout (l := l) T mu b = thetaPilotHullLogVolumeReal C3)

/-- The weighted q-side collapse: M4+M5a give the global same-C q readout
equality. -/
theorem S3131PaperRegionalQ_eq_of_modelMap
    (M : SameCModelMapResidual (l := l) T mu C3 P) :
    S3131PaperRegionalQ (l := l) T mu = qPilotLogVolumeReading P := by
  obtain ⟨_, _, _, _, hM4, hM5a, _⟩ := M
  unfold S3131PaperRegionalQ
  rw [Finset.sum_congr rfl (fun b _ => by rw [hM5a b])]
  rw [← Finset.sum_mul, hM4, one_mul]

/-- The weighted Theta-hull collapse: M4+M5b give the global same-C hull readout
equality. -/
theorem S3131PaperRegionalHull_eq_of_modelMap
    (M : SameCModelMapResidual (l := l) T mu C3 P) :
    S3131PaperRegionalHull (l := l) T mu = thetaPilotHullLogVolumeReal C3 := by
  obtain ⟨_, _, _, _, hM4, _, hM5b⟩ := M
  unfold S3131PaperRegionalHull
  rw [Finset.sum_congr rfl (fun b _ => by rw [hM5b b])]
  rw [← Finset.sum_mul, hM4, one_mul]

/-- The same-C readout bridge from the M-list (introduction form). -/
theorem sameCQThetaReadoutBridge_of_modelMap
    (M : SameCModelMapResidual (l := l) T mu C3 P) :
    SameCQThetaReadoutBridge (l := l) (T := T) (mu := mu) (C3 := C3) (P := P) := by
  refine ⟨?_, ?_⟩
  · exact (S3131PaperRegionalQ_eq_of_modelMap (l := l) T mu C3 P M).symm
  · exact (S3131PaperRegionalHull_eq_of_modelMap (l := l) T mu C3 P M).symm

/-- **R1 derivation from the model-map residual**: the named same-C readout
identification follows from the M-list by the proved weighted collapse. -/
theorem nativeToC3Identification_of_modelMap
    (M : SameCModelMapResidual (l := l) T mu C3 P) :
    NativeToC3SameCReadoutIdentification (l := l) T mu C3 P :=
  sameCQThetaReadoutBridge_of_modelMap (l := l) T mu C3 P M

/-- **Cor 3.12 signed comparison from the model-map residual** (via mainline's
unconditional paper-normalized comparison). -/
theorem qThetaPilotLogVolumeComparison_of_modelMap
    (M : SameCModelMapResidual (l := l) T mu C3 P) :
    qThetaPilotLogVolumeComparison C3 P :=
  qThetaPilotLogVolumeComparison_of_nativeIdentification (l := l) T mu C3 P
    (nativeToC3Identification_of_modelMap (l := l) T mu C3 P M)

/-- **Magnitude form** |log Theta| <= |log q| from the model-map residual. -/
theorem qThetaMagnitudeComparison_of_modelMap
    (M : SameCModelMapResidual (l := l) T mu C3 P) :
    -thetaPilotHullLogVolumeReal C3 <= -qPilotLogVolumeReading P :=
  qThetaMagnitudeComparison_of_nativeIdentification (l := l) T mu C3 P
    (nativeToC3Identification_of_modelMap (l := l) T mu C3 P M)

end LeanFormal.IUT.XiFPaper.S3137SameCModelMapResidualActual

namespace LeanFormal.IUT.Audit

/-- **Same-C model-map residual (final M-list).**  M0 native T<->OriginalInput
(IUT I Def 3.1); M1 Bad<->C3.tensorIndex (IUT I Def 3.1(b),(e); III Prop
3.4(ii)); M2 qVFamily q<->C3 q (I Ex 3.2(iv); III Def 3.8(i) p.112); M3 theta
values<->C3.thetaPacket (II Rem 2.5.1(i)); M4 variant-B raw weight total-one
(III Remark 3.1.1(ii)); M5a/M5b readout equalities (IV Prop 1.4(i); III Prop
3.9(i); Cor 3.12).  The weighted collapse to the two global same-C readout
equalities is proved; the residual is exactly the M-list. -/
def s3137SameCModelMapResidual : Obligation :=
  { id := "S3137.residual.same-C-model-map-M-list"
    source := "IUT I, Def 3.1, Ex. 3.2(iv); IUT II, Remark 2.5.1, (i); IUT III, Prop. 3.4, (ii), pp. 102-103; Prop. 3.9, (i), p. 115; Def. 3.8, (i), p. 112; Remark 3.1.1, (ii); IUT IV, Prop. 1.4, (i); Cor. 3.12"
    status := VerificationStatus.pending
    note := "R1 residual as the final M-list; M4+M5a/M5b collapse to the two same-C readout equalities is proved in S3137SameCModelMapResidualActual, and the signed Cor 3.12 comparison follows (via mainline S3131PaperRegionalQ_le_Hull).  M0-M3 cross-carrier matches are residual hypotheses, not asserted.  M4 variant B only (raw weight total-one); normalized-weight alternative total-one is qpilot S3131NormalizedWeightTotal."
    dependsOn := ["S3137SameCModelMapResidualActual", "S3137NativeToC3SameCReadoutActual", "S3131PaperNormalizedComparisonActual", "S3133S3131PlaceIndexComparisonActual"] }

end LeanFormal.IUT.Audit