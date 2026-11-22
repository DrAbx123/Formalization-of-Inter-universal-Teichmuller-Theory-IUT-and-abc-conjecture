import tmp.sheaf.xif.paper.S716PaperThetaHullLogSourceAuditActual
import tmp.sheaf.xif.paper.S669S663PaperXiFSourceLinkActual
import tmp.sheaf.xif.paper.S676FinalConditionalCor312Actual

-- S725: replace the s663 theta-average signed hull by the actual paper
-- root-hull log paperPerBThetaHullLog / globalThetaHullLog.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S725PaperHullCorrectedSourceLinkActual

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
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S657RootSignedHullIndependentActual
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

/-- Exact corrected paper signed-hull log: paperPerBThetaHullLog. -/
def PaperSignedHullCorrected (P : PaperSignedHull X label) : Prop :=
  P.signedHullLogVolume = -paperPerBThetaHullLog (l := l0) T b

/-- Conditional PaperXiFSourceLink using the corrected paper hull P. -/
noncomputable def s725PaperXiFSourceLink
    (hP : PaperSignedHullCorrected (l0 := l0) T b P)
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

noncomputable def s725PaperXiFInclusion
    (hP : PaperSignedHullCorrected (l0 := l0) T b P)
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
  link := s725PaperXiFSourceLink (T := T) (b := b) P O C3 hP hident hqpaper
    link_identification link_implies_inclusion
  link_holds := hlink

theorem s725_qPilot_mem_ray
    (hP : PaperSignedHullCorrected (l0 := l0) T b P)
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
    O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume :=
  (s725PaperXiFInclusion (T := T) (b := b) P O C3 hP hident hqpaper
    link_identification link_implies_inclusion hlink).qPilot_mem_ray

/-- Global corrected-vs-s663 average gap. -/
def GlobalPaperHullVsS663ThetaAverageGap : Prop :=
  globalThetaHullLog (l := l0) T =
    ∑ b : Bad (nativePlaceSelection T),
      nativeBadLocalWeight T b *
        (rootThetaMagnitudeProcession T b).average

def GlobalPaperHullVsS663ThetaAverageGapRequired : Prop :=
  GlobalPaperHullVsS663ThetaAverageGap (l0 := l0) T

#check s725PaperXiFSourceLink
#check s725PaperXiFInclusion
#check GlobalPaperHullVsS663ThetaAverageGap

end LeanFormal.IUT.XiFPaper.S725PaperHullCorrectedSourceLinkActual

end