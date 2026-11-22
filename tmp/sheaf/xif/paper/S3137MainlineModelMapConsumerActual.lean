import tmp.sheaf.xif.paper.S3131Stage2ModelMapActual
import tmp.sheaf.xif.paper.S3137QThetaComparisonBridgeActual
import LeanFormal.IUT.Audit.Status

/-!
# S3137: consume mainline's final same-C model map (R1 delta)

Mainline's final light model map (S3131Stage2ModelMapActual) is a component,
not a paper object:

  structure S3131Stage2ModelMapGlobal where
    arithmeticModelMatch : Prop     -- M0, IUT I Def 3.1
    badTensorIndexMatch : Prop      -- M1, IUT I Def 3.1(b),(e); III Prop 3.4(ii)
    qParameterMatch : Prop          -- M2, IUT I Ex 3.2(iv); III Def 3.8(i) p.112
    thetaValueMatch : Prop          -- M3, II Remark 2.5.1(i)
    qReadoutMatch : qPilotLogVolumeReading P = S3131PaperRegionalQ T mu
    hullReadoutMatch : thetaPilotHullLogVolumeReal C3 = S3131PaperRegionalHull T mu

with proved consumer nativeToC3Identification_of_modelMap producing my named
residual NativeToC3SameCReadoutIdentification.

This S3137 consumer file records the R1 delta: given the model map, the named
residual is produced by mainline's theorem, and the signed Cor 3.12 comparison
+ magnitude form follow from the S3137 bridge consumer chain (mainline's
unconditional paper-normalized same-coefficient comparison).  The only
residual content is the model map itself: the M0-M3 cross-carrier matches plus
the two concrete readout equalities (supplied as fields, NOT derivable from
mainline's definitions and NOT asserted here).  No carrier substitution, no
sorry, no axiom.  WRITE-ONLY.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137MainlineModelMapConsumerActual

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
open LeanFormal.IUT.XiFPaper.S3131PaperNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.S3131Stage2ModelMapActual
open LeanFormal.IUT.XiFPaper.S3131QCLeHCComparisonActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137NativeToC3SameCReadoutActual
open LeanFormal.IUT.XiFPaper.S3137QThetaComparisonBridgeActual
open MeasureTheory

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
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- **R1 derivation from mainline's final model map.** -/
theorem nativeToC3Identification_of_mainlineModelMap
    (M : S3131Stage2ModelMapGlobal T mu C3 P) :
    NativeToC3SameCReadoutIdentification (l := l) T mu C3 P :=
  S3131Stage2ModelMapActual.nativeToC3Identification_of_modelMap T mu C3 P M

/-- **Cor 3.12 signed comparison from mainline's final model map**, via the
S3137 bridge consumer chain and mainline's unconditional paper-normalized
same-coefficient comparison. -/
theorem qThetaPilotLogVolumeComparison_of_mainlineModelMap
    (M : S3131Stage2ModelMapGlobal T mu C3 P) :
    qThetaPilotLogVolumeComparison C3 P :=
  qThetaPilotLogVolumeComparison_of_nativeIdentification (l := l) T mu C3 P
    (nativeToC3Identification_of_mainlineModelMap (l := l) T mu C3 P M)

/-- **Magnitude form** |log Theta| <= |log q| from mainline's final model map. -/
theorem qThetaMagnitudeComparison_of_mainlineModelMap
    (M : S3131Stage2ModelMapGlobal T mu C3 P) :
    -thetaPilotHullLogVolumeReal C3 <= -qPilotLogVolumeReading P :=
  qThetaMagnitudeComparison_of_nativeIdentification (l := l) T mu C3 P
    (nativeToC3Identification_of_mainlineModelMap (l := l) T mu C3 P M)

/-- **R1 delta (contents of the residual).**  The only residual is the model map:
the M0-M3 cross-carrier Prop placeholders and the two concrete readout
equalities.  The comparison and its magnitude form are proved from it. -/
theorem r1_delta_recorded
    (M : S3131Stage2ModelMapGlobal T mu C3 P) :
    NativeToC3SameCReadoutIdentification (l := l) T mu C3 P ∧
      qThetaPilotLogVolumeComparison C3 P :=
  ⟨nativeToC3Identification_of_mainlineModelMap (l := l) T mu C3 P M,
    qThetaPilotLogVolumeComparison_of_mainlineModelMap (l := l) T mu C3 P M⟩

end LeanFormal.IUT.XiFPaper.S3137MainlineModelMapConsumerActual

namespace LeanFormal.IUT.Audit

/-- **R1 delta after mainline's final model map.**  The consumed model map
supplies M0-M3 as exact Prop placeholders (Missing, page refs in
S3131Stage2ModelMapActual) plus the two concrete readout equalities as fields;
it is not derivable from mainline's definitions and is not asserted here.  From
it the named residual NativeToC3SameCReadoutIdentification and the signed +
magnitude Cor 3.12 comparisons are proved in S3137MainlineModelMapConsumerActual.
Owner: lattice (consumer) + mainline (model-map fields) + qpilot (M1/place and
normalized-weight components). -/
def s3137R1MainlineModelMapDelta : Obligation :=
  { id := "S3137.residual.R1-delta-mainline-model-map"
    source := "IUT I, Def 3.1, Ex. 3.2(iv); IUT II, Remark 2.5.1, (i); IUT III, Prop. 3.4, (ii), pp. 102-103; Def. 3.8, (i), p. 112; Prop. 3.9, (i), p. 115; IUT IV, Prop. 1.4, (i); Cor. 3.12"
    status := VerificationStatus.pending
    note := "R1 delta: residual = model map (M0-M3 Prop placeholders + qReadoutMatch/hullReadoutMatch equalities); mainline nativeToC3Identification_of_modelMap gives the named residual; S3137 consumer proves signed + magnitude comparison via mainline's unconditional paper-normalized comparison.  M-fields are supplied, not asserted; concrete construction plan: Gaussian T model with C3.thetaPacket := FiniteThetaPacket.ofQ of the actual source q norm (M3 rfl), index/tensor transport for M1, qpilot qVFamTensorP_eq_base_val+M0 for M2, readout computations on the concrete model for M5; M4 variant B only if per-place form is used."
    dependsOn := ["S3131Stage2ModelMapActual", "S3137NativeToC3SameCReadoutActual", "S3137QThetaComparisonBridgeActual", "S3137MainlineModelMapConsumerActual"] }

end LeanFormal.IUT.Audit
