import tmp.sheaf.xif.paper.S658RootNormalizedPaperSignedHullActual
import tmp.sheaf.xif.paper.S660RootPaperSignedHullActual
import tmp.sheaf.xif.PaperXiFInclusion
import tmp.sheaf.n8.closure.SourcePilotRegion
/-! # S665: S658 PaperSignedHull vs PaperXiFSourceLink fields
S657/S658 fill the PaperSignedHull fields on the corrected positive root
procession.  PaperXiFSourceLink additionally needs the old qPilot object's
source identifications, the source-q equality, and the paper link fields;
this file gives the exact conditional constructor and exact requirements. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S665PaperSignedHullXiFInterfaceActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S657RootSignedHullIndependentActual
open LeanFormal.IUT.XiFPaper.S658RootNormalizedPaperSignedHullActual
open LeanFormal.IUT.XiFPaper.S660RootPaperSignedHullActual
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
universe ua uv upi umon ui uL uC uG uX uLabel uM uP
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable (A : IQHullLogVolumeInterface X)
variable (hnormal : A.logVolume A.hull = ENNReal.ofReal
  (rootThetaMagnitudeProcession T b).average)
/-- S658/s660 actual PaperSignedHull on the corrected root procession. -/
noncomputable def s665PaperSignedHull : PaperSignedHull X (SignedLabel l.value) :=
  s660PaperSignedHull (l := l) T b A hnormal
theorem s665_signedHullLogVolume_eq_neg_average :
    (s665PaperSignedHull T b A hnormal).signedHullLogVolume =
      -(rootThetaMagnitudeProcession T b).average :=
  s660_signedHullLogVolume_eq_neg_average T b A hnormal
theorem s665_average_nonneg :
    0 <= (s665PaperSignedHull T b A hnormal).procession.average :=
  (s665PaperSignedHull T b A hnormal).average_nonneg
/-- Conditional PaperXiFSourceLink constructor: all fields are explicit
parameters, including the old qPilot source identifications, the source-q
equality, and the paper link implication. -/
noncomputable def s665PaperXiFSourceLinkOf
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (C3 : SourcePilotRegionData I)
    (hsource : O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hq : O.qPilotLogVolume = paperQPilotLogVolume C3)
    (link_identification : Prop)
    (himp : link_identification →
      O.qPilotLogVolume ∈
        hullLogVolumeRay (s665PaperSignedHull T b A hnormal).signedHullLogVolume) :
    PaperXiFSourceLink O (s665PaperSignedHull T b A hnormal) C3 where
  source_identifications := hsource
  qPilotLogVolume_eq_paper := hq
  link_identification := link_identification
  link_implies_inclusion := himp
/-- Exact fields not supplied by S658 alone. -/
structure S665PaperXiFSourceLinkGap where
  source_identifications : Prop
  source_identifications_evidence : source_identifications
  qPilotLogVolume_eq_paper : Prop
  qPilotLogVolume_eq_paper_evidence : qPilotLogVolume_eq_paper
  link_identification : Prop
  link_implies_inclusion : Prop
def S665PaperXiFSourceLinkGapRequired : Prop :=
  Nonempty S665PaperXiFSourceLinkGap
end LeanFormal.IUT.XiFPaper.S665PaperSignedHullXiFInterfaceActual
