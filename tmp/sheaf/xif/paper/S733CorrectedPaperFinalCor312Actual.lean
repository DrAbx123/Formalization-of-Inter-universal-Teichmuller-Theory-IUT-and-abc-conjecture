import tmp.sheaf.xif.paper.S725PaperHullCorrectedSourceLinkActual
import tmp.sheaf.xif.paper.S676FinalConditionalCor312Actual
import tmp.sheaf.xif.paper.S716PaperThetaHullLogSourceAuditActual
import tmp.sheaf.xif.PaperAssembly

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S733CorrectedPaperFinalCor312Actual

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
open LeanFormal.IUT.XiFPaper.S716PaperThetaHullLogSourceAuditActual
open LeanFormal.IUT.XiFPaper.S725PaperHullCorrectedSourceLinkActual
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

/-- Corrected conditional P: signed log = -paperPerBThetaHullLog. -/
def S733CorrectedHullLog : Prop :=
  P.signedHullLogVolume = -paperPerBThetaHullLog (l := l0) T b

/-- Corrected source link built from the S725 corrected P. -/
noncomputable def s733SourceLink
    (hP : S733CorrectedHullLog P T b)
    (hident :
      O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hqpaper : S669QPilotLogVolumeEqPaper O C3)
    (link_identification : Prop)
    (link_implies_inclusion : link_identification →
      O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume) :
    PaperXiFSourceLink O P C3 :=
  s725PaperXiFSourceLink (T := T) (b := b) P O C3 hP hident hqpaper
    link_identification link_implies_inclusion

/-- Corrected conditional inclusion. -/
noncomputable def s733Inclusion
    (hP : S733CorrectedHullLog P T b)
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
    PaperXiFInclusion O P C3 :=
  s725PaperXiFInclusion (T := T) (b := b) P O C3 hP hident hqpaper
    link_identification link_implies_inclusion hlink

/-- Final conditional Cor312Conclusion with the corrected paper hull P. -/
theorem s733_finalCor312
    [Nonempty label]
    (hP : S733CorrectedHullLog P T b)
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
        (s733Inclusion (l := l) (V := V) (Label := Label) (Choice := Choice)
          (G' := G') (envStrip := envStrip) P O C3 T b hP hident hqpaper
          link_identification link_implies_inclusion hlink))).toStepXIFiniteCertificate) :
    Cor312Conclusion
      ((paperCertificate (I := paperXiFInput
        (s733Inclusion (l := l) (V := V) (Label := Label) (Choice := Choice)
          (G' := G') (envStrip := envStrip) P O C3 T b hP hident hqpaper
          link_identification link_implies_inclusion hlink))).toContract
        (paperSignedLinkEvidence
          (I := paperXiFInput
            (s733Inclusion (l := l) (V := V) (Label := Label) (Choice := Choice)
              (G' := G') (envStrip := envStrip) P O C3 T b hP hident hqpaper
              link_identification link_implies_inclusion hlink)) links)) := by
  exact paperAssembly_cor312Conclusion
    (link := s733SourceLink (l := l) (V := V) (Label := Label) (Choice := Choice)
      (G' := G') (envStrip := envStrip) P O C3 T b
      hP hident hqpaper link_identification link_implies_inclusion)
    (link_holds := hlink) (links := links)


/-- Explicit corrected signed log of the conditional paper hull P. -/
theorem s733_signed_log
    (hP : S733CorrectedHullLog P T b) :
    P.signedHullLogVolume = -paperPerBThetaHullLog (l := l0) T b :=
  hP

end LeanFormal.IUT.XiFPaper.S733CorrectedPaperFinalCor312Actual

end
