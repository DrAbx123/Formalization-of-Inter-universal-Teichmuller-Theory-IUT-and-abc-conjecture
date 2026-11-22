import tmp.sheaf.xif.paper.S2708MultiPlaceQPilotActual
import tmp.sheaf.xif.PaperXiFInclusion

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2712MultiQConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper

universe ua uv upi umon ui uG uL uC uX uLabel

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]

/-- Multi-q source link: same source identifications and link implication as
PaperXiFSourceLink, but the paper scalar field is the multi-place q-pilot
volume. -/
structure MultiQPaperXiFSourceLink
    (O : PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
      I G envStrip)
    (P : PaperSignedHull X label)
    (D : MultiPlaceQPilotDonor I) where
  source_identifications :
    O.paper_strip_identification ∧
    O.paper_lineBundle_identification ∧
    O.paper_logKummer_identification ∧
    O.paper_qPilot_log_identification
  qPilotLogVolume_eq_multi :
    O.qPilotLogVolume = paperQPilotLogVolume_multi D
  link_identification : Prop
  link_implies_inclusion :
    link_identification →
      O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume

structure MultiQPaperXiFInclusion
    (O : PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
      I G envStrip)
    (P : PaperSignedHull X label)
    (D : MultiPlaceQPilotDonor I) where
  link : MultiQPaperXiFSourceLink O P D
  link_holds : link.link_identification

namespace MultiQPaperXiFInclusion

variable {O : PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
  I G envStrip}
variable {P : PaperSignedHull X label}
variable {D : MultiPlaceQPilotDonor I}

theorem qPilot_mem_ray (J : MultiQPaperXiFInclusion O P D) :
    O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume :=
  J.link.link_implies_inclusion J.link_holds

theorem qPilot_le_signedHull (J : MultiQPaperXiFInclusion O P D) :
    O.qPilotLogVolume ≤ P.signedHullLogVolume :=
  (mem_hullLogVolumeRay_iff).mp J.qPilot_mem_ray

theorem qPilotLogVolume_eq_multi (J : MultiQPaperXiFInclusion O P D) :
    O.qPilotLogVolume = paperQPilotLogVolume_multi D :=
  J.link.qPilotLogVolume_eq_multi

end MultiQPaperXiFInclusion

/-- Build the multi-q consumer from any PaperQPilotObject, a multi-place donor,
and the explicit inequality hcomp.  The scalar field is definitional. -/
noncomputable def multiQPaperXiFSourceLink
    (O : PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
      I G envStrip)
    (P : PaperSignedHull X label)
    (D : MultiPlaceQPilotDonor I)
    (hstrip : O.paper_strip_identification)
    (hline : O.paper_lineBundle_identification)
    (hlog : O.paper_logKummer_identification)
    (hqPilot : O.paper_qPilot_log_identification)
    (hcomp : O.qPilotLogVolume ≤ P.signedHullLogVolume) :
    MultiQPaperXiFSourceLink O P D where
  source_identifications := ⟨hstrip, hline, hlog, hqPilot⟩
  qPilotLogVolume_eq_multi :=
    paperQPilotObject_qPilotLogVolume_eq_multi O D
  link_identification := O.qPilotLogVolume ≤ P.signedHullLogVolume
  link_implies_inclusion := fun h => (mem_hullLogVolumeRay_iff).mpr h

noncomputable def multiQPaperXiFInclusion
    (O : PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
      I G envStrip)
    (P : PaperSignedHull X label)
    (D : MultiPlaceQPilotDonor I)
    (hstrip : O.paper_strip_identification)
    (hline : O.paper_lineBundle_identification)
    (hlog : O.paper_logKummer_identification)
    (hqPilot : O.paper_qPilot_log_identification)
    (hcomp : O.qPilotLogVolume ≤ P.signedHullLogVolume) :
    MultiQPaperXiFInclusion O P D where
  link := multiQPaperXiFSourceLink O P D hstrip hline hlog hqPilot hcomp
  link_holds := hcomp

#check MultiQPaperXiFSourceLink
#check MultiQPaperXiFInclusion
#check MultiQPaperXiFInclusion.qPilot_le_signedHull
#check multiQPaperXiFInclusion
#print axioms MultiQPaperXiFInclusion.qPilot_le_signedHull
end LeanFormal.IUT.XiFPaper.S2712MultiQConsumerActual
end
