import tmp.sheaf.xif.paper.ThetaLinkFromSource
import tmp.sheaf.xif.PaperXiFInclusion

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S638ActualToPaperXiFSourceLinkActualAdapted
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
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

variable (hident :
  O.paper_strip_identification ∧
  O.paper_lineBundle_identification ∧
  O.paper_logKummer_identification ∧
  O.paper_qPilot_log_identification)
variable (hqpaper : O.qPilotLogVolume = paperQPilotLogVolume C3)
variable (hq : O.qPilotLogVolume = Oa.signedQPilotLogVolume)

noncomputable def paperXiFSourceLinkOfActual :
    PaperXiFSourceLink O P C3 where
  source_identifications := hident
  qPilotLogVolume_eq_paper := hqpaper
  link_identification := (actualThetaLink Oa P).link_identification
  link_implies_inclusion := by
    intro h
    have hmem := (actualThetaLink Oa P).link_implies_inclusion h
    rw [← hq] at hmem
    exact hmem

end LeanFormal.IUT.XiFPaper.S638ActualToPaperXiFSourceLinkActualAdapted
end
