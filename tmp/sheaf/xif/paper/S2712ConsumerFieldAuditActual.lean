import tmp.sheaf.xif.paper.S2711HcompMultiActual
import tmp.sheaf.xif.PaperXiFInclusion

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2712ConsumerFieldAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.XiFPaper.S2711HcompMultiActual

universe ua uv upi umon ui uL uC uG uX uLabel

variable {l : PrimeGeFive} {V : Type uv}
  {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
  {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
  {G : Type uG} [Group G] [TopologicalSpace G]
  {envStrip : FPrimeStrip V}

/-- The migrated multi-place object keeps the original paper strip
identification field definitionally. -/
theorem S2712_multi_paper_strip
    (O : PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
      I G envStrip)
    (D : MultiPlaceQPilotDonor I) :
    (paperQPilotObject_multi O D).paper_strip_identification =
      O.paper_strip_identification := rfl

theorem S2712_multi_paper_lineBundle
    (O : PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
      I G envStrip)
    (D : MultiPlaceQPilotDonor I) :
    (paperQPilotObject_multi O D).paper_lineBundle_identification =
      O.paper_lineBundle_identification := rfl

theorem S2712_multi_paper_logKummer
    (O : PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
      I G envStrip)
    (D : MultiPlaceQPilotDonor I) :
    (paperQPilotObject_multi O D).paper_logKummer_identification =
      O.paper_logKummer_identification := rfl

theorem S2712_multi_paper_qPilot_log
    (O : PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
      I G envStrip)
    (D : MultiPlaceQPilotDonor I) :
    (paperQPilotObject_multi O D).paper_qPilot_log_identification =
      O.paper_qPilot_log_identification := rfl

/-- The replacement for `PaperXiFSourceLink.link_implies_inclusion` at the
multi-place object: the q-pilot scalar lies in the signed-hull ray. -/
theorem S2712_multi_membership
    (O : PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
      I G envStrip)
    (D : MultiPlaceQPilotDonor I)
    {X : Type uX} {label : Type uLabel} [Fintype label]
    (P : PaperSignedHull X label)
    (hP : P.procession.average = 2 * Real.log 5)
    (hbad : 2 * Real.log 5 < sourceBadQAbsLog I.initial) :
    (paperQPilotObject_multi O D).qPilotLogVolume ∈
      hullLogVolumeRay P.signedHullLogVolume :=
  concreteMembership_of_sourceComparison (paperQPilotObject_multi O D) P
    (S2711_hcomp_multi O D P hP hbad)

#check S2712_multi_paper_strip
#check S2712_multi_paper_lineBundle
#check S2712_multi_paper_logKummer
#check S2712_multi_paper_qPilot_log
#check S2712_multi_membership
#print axioms S2712_multi_membership

end LeanFormal.IUT.XiFPaper.S2712ConsumerFieldAuditActual
end
