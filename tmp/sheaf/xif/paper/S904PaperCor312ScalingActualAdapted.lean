import tmp.sheaf.xif.paper.S898PaperGapFromScalingActual

-- S904: final conditional Cor312 from S898 paper gap fields.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S904PaperCor312ScalingActualAdapted

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
open LeanFormal.IUT.XiFPaper.S898PaperGapFromScalingActual
open LeanFormal.IUT.XiFPaper.S881PaperGapIntrinsicVolumeS869Actual
open LeanFormal.IUT.XiFPaper.S858PaperGapConditionalCor312Actual
open LeanFormal.IUT.XiFPaper.S669S663PaperXiFSourceLinkActual
open MeasureTheory

universe ua uv upi umon ui uL uC uG uW uX uLabel uK

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

noncomputable def s904PaperGap
    (hP : S898SignedHullThetaInterface (l := l0) T b P)
    (hHull : S881HullLogExactGap (l := l0) T b) :
    PaperGap (l := l0) T b P :=
  paperGapFromScaling (l := l0) T b P hP hHull

theorem paperCor312_of_scaling
    [Nonempty label]
    (hP : S898SignedHullThetaInterface (l := l0) T b P)
    (hHull : S881HullLogExactGap (l := l0) T b)
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
          (G' := G') (envStrip := envStrip) P O C3 T b
          (s904PaperGap (l := l0) T b P hP hHull).signed_hull_log_eq
          hident hqpaper link_identification link_implies_inclusion hlink))).toStepXIFiniteCertificate) :
    Cor312Conclusion
      ((paperCertificate (I := paperXiFInput
        (s858Inclusion (l := l) (V := V) (Label := Label) (Choice := Choice)
          (G' := G') (envStrip := envStrip) P O C3 T b
          (s904PaperGap (l := l0) T b P hP hHull).signed_hull_log_eq
          hident hqpaper link_identification link_implies_inclusion hlink))).toContract
        (paperSignedLinkEvidence
          (I := paperXiFInput
            (s858Inclusion (l := l) (V := V) (Label := Label) (Choice := Choice)
              (G' := G') (envStrip := envStrip) P O C3 T b
              (s904PaperGap (l := l0) T b P hP hHull).signed_hull_log_eq
              hident hqpaper link_identification link_implies_inclusion hlink)) links)) :=
  paperCor312_of_gap (l := l0) (V := V) (Label := Label) (Choice := Choice)
    (G' := G') (envStrip := envStrip) P O C3 T b
    (s904PaperGap (l := l0) T b P hP hHull)
    hident hqpaper link_identification link_implies_inclusion hlink links

#check paperCor312_of_scaling

end LeanFormal.IUT.XiFPaper.S904PaperCor312ScalingActualAdapted

end