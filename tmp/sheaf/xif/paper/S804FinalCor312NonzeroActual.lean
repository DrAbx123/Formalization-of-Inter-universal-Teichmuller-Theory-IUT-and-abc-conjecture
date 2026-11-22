import tmp.sheaf.xif.paper.S779RootHullNonzeroFixActual
import tmp.sheaf.xif.paper.S669S663PaperXiFSourceLinkActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S804FinalCor312NonzeroActual

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
open LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual
open LeanFormal.IUT.XiFPaper.S669S663PaperXiFSourceLinkActual
open MeasureTheory

universe ua uv upi umon ui uL uC uG uX uLabel uK
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

def S804CorrectedHullLog (P : PaperSignedHull X label) : Prop :=
  P.signedHullLogVolume =
    paperRootThetaHullLogNonzero (l := l0) T b Measure.addHaar

noncomputable def s804SourceLink
    (hP : S804CorrectedHullLog (l0 := l0) T b P)
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

noncomputable def s804Inclusion
    (hP : S804CorrectedHullLog (l0 := l0) T b P)
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
  link := s804SourceLink P O C3 (l0 := l0) T b hP hident hqpaper
    link_identification link_implies_inclusion
  link_holds := hlink

end LeanFormal.IUT.XiFPaper.S804FinalCor312NonzeroActual
end