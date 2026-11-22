import tmp.sheaf.xif.paper.S2711PaperMultiUnconditionalActual
import tmp.sheaf.xif.paper.ThetaLinkActual
import tmp.sheaf.xif.paper.S2704S2696SourceDataActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2718ThetaLinkPartialActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual
open LeanFormal.IUT.XiFPaper.ThetaLink
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open scoped BigOperators

universe ua uv upi umon ui uG uL uC uX uLabel
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]

/-- The seven ThetaLinkActual fields that the multi-q data can provide; only
qPilotLogVolume_eq_paper (the single-C3 paper volume) is omitted. -/
structure ThetaLinkActualPartial
    (O : PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
      I G envStrip)
    (P : PaperSignedHull X label) where
  qPilot_identifications : thetaLinkQPilotPaperIdentifications O
  qParameter : Real
  qParameter_pos : 0 < qParameter
  qParameter_log_ne_zero : Real.log qParameter ≠ 0
  qPilotLogVolume_eq_neg_abs : O.qPilotLogVolume = -|Real.log qParameter|
  link_identification : Prop
  link_implies_inclusion :
    link_identification →
      O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume

namespace ThetaLinkActualPartial

variable {O : PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
  I G envStrip}
variable {P : PaperSignedHull X label}

/-- Build the partial Theta-link from any multi-q paper data whose q-pilot
scalar is negative.  qParameter := exp(O.qPilotLogVolume) realises the
-|log qParameter| field without any single completion q. -/
noncomputable def ofMultiQ
    (M : PaperUnconditionalDataMulti (l := l) (V := V) v O D P)
    (hneg : O.qPilotLogVolume < 0) :
    ThetaLinkActualPartial O P where
  qPilot_identifications := M.sourceLink.source_identifications
  qParameter := Real.exp O.qPilotLogVolume
  qParameter_pos := Real.exp_pos _
  qParameter_log_ne_zero := by
    rw [Real.log_exp]
    exact ne_of_lt hneg
  qPilotLogVolume_eq_neg_abs := by
    rw [Real.log_exp, abs_of_neg hneg, neg_neg]
  link_identification := O.qPilotLogVolume ≤ P.signedHullLogVolume
  link_implies_inclusion := fun h => (mem_hullLogVolumeRay_iff).mpr h

/-- The exact missing field: adding the single-C3 paper q volume equality
turns a partial Theta-link into a full ThetaLinkActual. -/
def toThetaLinkActual
    (L : ThetaLinkActualPartial O P)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (hpaper : O.qPilotLogVolume = paperQPilotLogVolume C3) :
    ThetaLinkActual O P C3 where
  qPilot_identifications := L.qPilot_identifications
  qPilotLogVolume_eq_paper := hpaper
  qParameter := L.qParameter
  qParameter_pos := L.qParameter_pos
  qParameter_log_ne_zero := L.qParameter_log_ne_zero
  qPilotLogVolume_eq_neg_abs := L.qPilotLogVolume_eq_neg_abs
  link_identification := L.link_identification
  link_implies_inclusion := L.link_implies_inclusion

theorem toThetaLinkActual_qPilotLogVolume_eq_paper
    (L : ThetaLinkActualPartial O P)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (hpaper : O.qPilotLogVolume = paperQPilotLogVolume C3) :
    (toThetaLinkActual L C3 hpaper).qPilotLogVolume_eq_paper = hpaper := rfl

end ThetaLinkActualPartial

end LeanFormal.IUT.XiFPaper.S2718ThetaLinkPartialActual
end
