import tmp.sheaf.xif.paper.ThetaLinkFromSource
import tmp.sheaf.xif.PaperXiFInclusion

/-! # S983: PaperXiFSourceLink construction from actual components

source_identifications: supplied explicit source-identification conjunction
(actual for the concrete object via ConcreteQPilotLogIdentificationActual).
qPilotLogVolume_eq_paper: supplied exact source-q identification (the concrete
actual theorem concreteO_qPilotLogVolume_eq_paper).
link_identification: the actual ThetaLinkFromSource comparison thetaSourceComparison.
link_implies_inclusion: the actual actualThetaLink implication, transported from
Oa.signedQPilotLogVolume to O.qPilotLogVolume by the supplied signed-q equality.
No fake link field is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S983PaperXiFSourceLinkConstructionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ThetaLinkFromSource

universe ua uv upi umon ui uC3 uD3 uM uP uG uL uC uX uLabel

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (O : PaperQPilotObject (l := l) (V := V)
  (Label := Label) (Choice := Choice) I G envStrip)
variable (Oa : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP}
  (l := l) (V := V) (I := I))
variable (P : PaperSignedHull X label)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- Construct PaperXiFSourceLink from the actual Theta link. -/
noncomputable def paperXiFSourceLinkOfActualTheta
    (hident :
      O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hqpaper : O.qPilotLogVolume = paperQPilotLogVolume C3)
    (hq : O.qPilotLogVolume = Oa.signedQPilotLogVolume) :
    PaperXiFSourceLink O P C3 where
  source_identifications := hident
  qPilotLogVolume_eq_paper := hqpaper
  link_identification := (actualThetaLink Oa P).link_identification
  link_implies_inclusion := by
    intro h
    have hmem := (actualThetaLink Oa P).link_implies_inclusion h
    rw [← hq] at hmem
    exact hmem

/-- The constructed link's identification is the actual source comparison. -/
theorem paperXiFSourceLinkOfActualTheta_link_identification
    (hident :
      O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hqpaper : O.qPilotLogVolume = paperQPilotLogVolume C3)
    (hq : O.qPilotLogVolume = Oa.signedQPilotLogVolume) :
    (paperXiFSourceLinkOfActualTheta O Oa P C3 hident hqpaper hq).link_identification =
      thetaSourceComparison Oa P := by
  rfl

/-- Exact minimal remaining data for the link: source identifications, the
paper q normalization, and the actual Theta-link signed-q identification. -/
structure S983LinkInputs : Prop where
  source_identifications :
    O.paper_strip_identification ∧
    O.paper_lineBundle_identification ∧
    O.paper_logKummer_identification ∧
    O.paper_qPilot_log_identification
  qPilotLogVolume_eq_paper : O.qPilotLogVolume = paperQPilotLogVolume C3
  signed_q_identification : O.qPilotLogVolume = Oa.signedQPilotLogVolume

/-- Inputs give the actual source link. -/
noncomputable def paperXiFSourceLink_of_inputs
    (h : S983LinkInputs (l := l) (V := V) (I := I) (O := O) (Oa := Oa) (C3 := C3)) :
    PaperXiFSourceLink O P C3 :=
  paperXiFSourceLinkOfActualTheta O Oa P C3
    h.source_identifications h.qPilotLogVolume_eq_paper h.signed_q_identification

end LeanFormal.IUT.XiFPaper.S983PaperXiFSourceLinkConstructionActual

end
