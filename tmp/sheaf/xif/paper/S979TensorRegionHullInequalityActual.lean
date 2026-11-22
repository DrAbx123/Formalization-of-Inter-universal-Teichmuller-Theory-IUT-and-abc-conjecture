import tmp.sheaf.xif.paper.S971TensorRegionImageActual
import tmp.sheaf.xif.paper.S962TensorPacketPaperInequalityActual
import tmp.sheaf.xif.paper.S968FinalTensorInequalityCor312Actual

/-! # S979: qPilot tensor log <= tensorRegionHull log

Uses S971's actual qPilotPaperImage_subset_tensorRegionHull, so the old point
density condition is replaced by an actual region-image containment.
Only positivity of the qPilot image measure and finiteness of the
tensorRegionHull measure are needed for the per-b and weighted inequalities.
The final Cor312 assembly is re-exported from S968 with the new inequality.
No equality/scaling data. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S979TensorRegionHullInequalityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedThetaIndHullActual
open LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual
open LeanFormal.IUT.XiFPaper.S956TensorPacketLogVolumeExactActual
open LeanFormal.IUT.XiFPaper.S971TensorRegionImageActual
open LeanFormal.IUT.XiFPaper.S962TensorPacketPaperInequalityActual
open LeanFormal.IUT.XiFPaper.S968FinalTensorInequalityCor312Actual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open MeasureTheory

universe ua uv upi umon ui uL uC uG uW uX uLabel uK u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Normalized log-volume on the actual tensor region hull. -/
noncomputable def tensorRegionHullLog
    (D : FinalLTensorLogVolumeData (l := l) T b) : Real :=
  tensorNormalizedLogVolume (l := l) T b D
    (tensorRegionHull (l := l) T b D)

/-- Per-b inequality: qPilot tensor log <= tensorRegionHull log. -/
theorem qPilotTensorLog_le_tensorRegionHullLog
    (D : FinalLTensorLogVolumeData (l := l) T b)
    (hpos : 0 < D.measure (qPilotPaperImageInLValued (l := l) T b))
    (hfin : D.measure (tensorRegionHull (l := l) T b D) < ⊤) :
    qPilotTensorLog (l := l) T b D ≤
      tensorRegionHullLog (l := l) T b D :=
  tensorNormalizedLogVolume_mono (l := l) T b D
    (qPilotPaperImage_subset_tensorRegionHull (l := l) T b D) hpos hfin

/-- Exactly the positivity/finiteness hypotheses, no density. -/
def S979TensorRegionHypotheses
    (D : ∀ b : Bad (nativePlaceSelection T),
      FinalLTensorLogVolumeData (l := l) T b) : Prop :=
  (∀ b : Bad (nativePlaceSelection T),
    0 < (D b).measure (qPilotPaperImageInLValued (l := l) T b)) ∧
  (∀ b : Bad (nativePlaceSelection T),
    (D b).measure (tensorRegionHull (l := l) T b (D b)) < ⊤)

/-- Global weighted inequality with the actual region hull. -/
noncomputable def tensorRegionHullPaperWeightedInequality
    (D : ∀ b : Bad (nativePlaceSelection T),
      FinalLTensorLogVolumeData (l := l) T b) : Prop :=
  weightedPaperV (l := l) T
      (fun b => qPilotTensorLog (l := l) T b (D b)) ≤
    weightedPaperV (l := l) T
      (fun b => tensorRegionHullLog (l := l) T b (D b))

theorem tensorRegionHullPaperWeightedInequality_of_perB
    (D : ∀ b : Bad (nativePlaceSelection T),
      FinalLTensorLogVolumeData (l := l) T b)
    (h : S979TensorRegionHypotheses (l := l) T D) :
    tensorRegionHullPaperWeightedInequality (l := l) T D := by
  obtain ⟨hpos, hfin⟩ := h
  unfold tensorRegionHullPaperWeightedInequality
  apply weightedPaperV_mono (l := l) T
  intro b
  exact qPilotTensorLog_le_tensorRegionHullLog (l := l) T b (D b) (hpos b) (hfin b)

/-- Final conditional assembly: region-hull positivity/finiteness plus source
link and finite links imply the actual weighted inequality and Cor312. -/
theorem paperCor312_of_tensorRegionInequality
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    {G' : Type uG} [Group G'] [TopologicalSpace G']
    {envStrip : FPrimeStrip V}
    {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]
    (P : PaperSignedHull X label)
    (O : PaperQPilotObject (l := l) (V := V)
      (Label := Label) (Choice := Choice) (I := I) G' envStrip)
    (C3 : SourcePilotRegionData I)
    (D : ∀ b : Bad (nativePlaceSelection T),
      FinalLTensorLogVolumeData (l := l) T b)
    (h : S979TensorRegionHypotheses (l := l) T D)
    (link : PaperXiFSourceLink O P C3)
    (hlink : link.link_identification)
    (links : FiniteStepXILinkEvidence
      (paperCertificate (I := paperXiFInput
        (s968Inclusion (l := l) (V := V) (Label := Label) (Choice := Choice)
          (G' := G') (envStrip := envStrip) P O C3 link hlink))).toStepXIFiniteCertificate) :
    tensorRegionHullPaperWeightedInequality (l := l) T D ∧
      Cor312Conclusion
        ((paperCertificate (I := paperXiFInput
          (s968Inclusion (l := l) (V := V) (Label := Label) (Choice := Choice)
            (G' := G') (envStrip := envStrip) P O C3 link hlink))).toContract
          (paperSignedLinkEvidence
            (I := paperXiFInput
              (s968Inclusion (l := l) (V := V) (Label := Label) (Choice := Choice)
                (G' := G') (envStrip := envStrip) P O C3 link hlink)) links)) := by
  constructor
  · exact tensorRegionHullPaperWeightedInequality_of_perB (l := l) T D h
  · exact paperAssembly_cor312Conclusion
      (link := link) (link_holds := hlink) (links := links)

end LeanFormal.IUT.XiFPaper.S979TensorRegionHullInequalityActual

end
