import tmp.sheaf.xif.paper.S733CorrectedPaperFinalCor312Actual
import tmp.sheaf.xif.paper.S804FinalCor312NonzeroActual
import tmp.sheaf.xif.paper.S814PaperHullLogInterfaceActual
import tmp.sheaf.xif.paper.S790StackToPaperQPilotThetaActual
import tmp.sheaf.xif.paper.S797PaperHullFirstAuditActual
import tmp.sheaf.xif.paper.S669S663PaperXiFSourceLinkActual
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier
import tmp.sheaf.xif.paper.S810LeastHullPaperCarrierActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S858PaperGapConditionalCor312Actual

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
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S733CorrectedPaperFinalCor312Actual
open LeanFormal.IUT.XiFPaper.S797PaperHullFirstAuditActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.S669S663PaperXiFSourceLinkActual
open LeanFormal.IUT.XiFPaper.S810LeastHullPaperCarrierActual
open LeanFormal.IUT.XiFPaper.S790StackToPaperQPilotThetaActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open MeasureTheory

universe ua uv upi umon ui uL uC uG uW uX uLabel uK uD
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {G' : Type uG} [Group G'] [TopologicalSpace G']
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (P : PaperSignedHull X label)
variable (O : PaperQPilotObject (l := l) (V := V)
  (Label := Label) (Choice := Choice) (I := I) G' envStrip)
variable (C3 : SourcePilotRegionData I)
variable {l0 : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l0)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Intrinsic log-shell normalization datum for the paper gap.  No inhabitant
is asserted. -/
structure PaperGapIntrinsicVolume where
  D : SourceLogShellDatum.{uD}
  rootUnit : D.Units
  volumeLog : D.K →+ Real
  /-- V(root) = -order/(2l) * log p, paper sign. -/
  root_value_eq :
    volumeLog ((D.logMap rootUnit).toAdd) =
      -((((qVFamily T b).order : Real) / (2 * (l.value : Real))) *
        Real.log (D.p : Real))
  /-- The least-hull normalized log is the intrinsic root volume. -/
  hull_log_eq_root :
    paperLeastLambdaOHullLog (l := l0) T b Measure.addHaar =
      volumeLog ((D.logMap rootUnit).toAdd)

/-- Paper gap: corrected signed hull equal to the least-hull normalized log,
plus an intrinsic log-shell volume realizing the root normalization. -/
structure PaperGap (P : PaperSignedHull X label) where
  signed_hull_log_eq :
    P.signedHullLogVolume =
      paperLeastLambdaOHullLog (l := l0) T b Measure.addHaar
  intrinsic : PaperGapIntrinsicVolume (l := l) T b

/-- The gap's hull is the S797/S810 corrected least hull. -/
theorem paperGap_hull_eq_S797 :
    paperLeastLambdaOHull (l := l0) T b =
      S797PaperHullFirstAuditActual.paperHullFirstCarrierCorrected (l := l0) T b :=
  rfl

/-- The S790 qPilot region is contained in the gap's least hull. -/
theorem paperGap_qPilot_subset :
    paperStackQPilotRegion (l := l0) T b ⊆
      paperLeastLambdaOHull (l := l0) T b := by
  exact (paperStackQPilotRegion_eq_corrected (l := l0) T b).le.trans
    (paperQPilotRegionCorrected_subset_least (l := l0) T b)

/-- Conditional source link from the paper gap. -/
noncomputable def s858SourceLink
    (hP : P.signedHullLogVolume =
      paperLeastLambdaOHullLog (l := l0) T b Measure.addHaar)
    (hident :
      O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hqpaper : S669QPilotLogVolumeEqPaper O C3)
    (link_identification : Prop)
    (link_implies_inclusion : link_identification →
      O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume) :
    PaperXiFSourceLink O P C3 where
  source_identifications := hident
  qPilotLogVolume_eq_paper := hqpaper
  link_identification := link_identification
  link_implies_inclusion := link_implies_inclusion

/-- Conditional inclusion from the paper gap. -/
noncomputable def s858Inclusion
    (hP : P.signedHullLogVolume =
      paperLeastLambdaOHullLog (l := l0) T b Measure.addHaar)
    (hident :
      O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hqpaper : S669QPilotLogVolumeEqPaper O C3)
    (link_identification : Prop)
    (link_implies_inclusion : link_identification →
      O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume)
    (hlink : link_identification) :
    PaperXiFInclusion O P C3 where
  link := s858SourceLink P O C3 (l0 := l0) T b hP hident hqpaper
    link_identification link_implies_inclusion
  link_holds := hlink

/-- Paper-faithful conditional Cor312 interface: assumes the paper gap,
then assembles the actual source/inclusion chain. -/
theorem paperCor312_of_gap
    [Nonempty label]
    (h : PaperGap (l := l0) T b P)
    (hident :
      O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hqpaper : S669QPilotLogVolumeEqPaper O C3)
    (link_identification : Prop)
    (link_implies_inclusion : link_identification →
      O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume)
    (hlink : link_identification)
    (links : FiniteStepXILinkEvidence
      (paperCertificate (I := paperXiFInput
        (s858Inclusion (l := l) (V := V) (Label := Label) (Choice := Choice)
          (G' := G') (envStrip := envStrip) P O C3 T b h.signed_hull_log_eq
          hident hqpaper link_identification link_implies_inclusion hlink))).toStepXIFiniteCertificate) :
    Cor312Conclusion
      ((paperCertificate (I := paperXiFInput
        (s858Inclusion (l := l) (V := V) (Label := Label) (Choice := Choice)
          (G' := G') (envStrip := envStrip) P O C3 T b h.signed_hull_log_eq
          hident hqpaper link_identification link_implies_inclusion hlink))).toContract
        (paperSignedLinkEvidence
          (I := paperXiFInput
            (s858Inclusion (l := l) (V := V) (Label := Label) (Choice := Choice)
              (G' := G') (envStrip := envStrip) P O C3 T b h.signed_hull_log_eq
              hident hqpaper link_identification link_implies_inclusion hlink)) links)) := by
  exact paperAssembly_cor312Conclusion
    (link := s858SourceLink P O C3 (l0 := l0) T b h.signed_hull_log_eq
      hident hqpaper link_identification link_implies_inclusion)
    (link_holds := hlink) (links := links)

end LeanFormal.IUT.XiFPaper.S858PaperGapConditionalCor312Actual

end
