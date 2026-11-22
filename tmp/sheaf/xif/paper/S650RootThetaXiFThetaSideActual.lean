import tmp.sheaf.xif.paper.S658RootNormalizedPaperSignedHullActual
import tmp.sheaf.xif.PaperXiFInclusion

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S650RootThetaXiFThetaSideActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S657RootSignedHullIndependentActual
open LeanFormal.IUT.XiFPaper.S658RootNormalizedPaperSignedHullActual
open MeasureTheory
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume

universe ua uv upi umon ui uL uC uG uX uLabel
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {G' : Type uG} [Group G'] [TopologicalSpace G']
variable {envStrip : FPrimeStrip V}
variable {X : Type uX}
/-- Conditional PaperXiFSourceLink whose theta side is the actual root-normalized
paper signed hull.  Source-q and link fields remain explicit hypotheses. -/
noncomputable def paperXiFSourceLinkOfRootThetaHull
    (T : SourceNativeInitialThetaData l)
    (b : Bad (nativePlaceSelection T))
    {X : Type uX} (A : IQHullLogVolumeInterface X)
    (hnormal : A.logVolume A.hull = ENNReal.ofReal
      (rootThetaMagnitudeProcession T b).average)
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) (I := I) G' envStrip)
    (C3 : SourcePilotRegionData I)
    (hident :
      O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hqpaper : O.qPilotLogVolume = paperQPilotLogVolume C3)
    (link_identification : Prop)
    (link_implies_inclusion : link_identification →
      O.qPilotLogVolume ∈
        hullLogVolumeRay (S658RootNormalizedPaperSignedHullActual.rootNormalizedPaperSignedHullCorrected T b A hnormal).signedHullLogVolume) :
    PaperXiFSourceLink O (S658RootNormalizedPaperSignedHullActual.rootNormalizedPaperSignedHullCorrected T b A hnormal) C3 where
  source_identifications := hident
  qPilotLogVolume_eq_paper := hqpaper
  link_identification := link_identification
  link_implies_inclusion := link_implies_inclusion

end LeanFormal.IUT.XiFPaper.S650RootThetaXiFThetaSideActual
end