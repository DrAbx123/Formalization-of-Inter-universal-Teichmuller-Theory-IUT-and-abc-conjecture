import tmp.sheaf.xif.PaperXiFInclusion

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S674SourceQIdentificationPackageActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotLogVolume

universe ua uv upi umon ui uL uC uG uX uLabel
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
variable (P : PaperSignedHull X label)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- Exact source-q identification needed for qPilotLogVolume_eq_paper. -/
def ConcreteSourceQIdentification
    (I : OriginalInput.{ua,uv,upi,umon,ui} l V)
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Prop :=
  sourceQPilotSignedLog I.initial = localSignedLog C3.q

/-- The paper q-pilot log equality is exactly the source-q identification. -/
theorem qPilotLogVolume_eq_paper_iff_sourceQ :
    O.qPilotLogVolume = paperQPilotLogVolume C3 ↔
      ConcreteSourceQIdentification I C3 := by
  unfold ConcreteSourceQIdentification
  rw [O.qPilotLogVolume_eq]
  unfold paperQPilotLogVolume
  rfl

/-- Conditional qPilotLogVolume_eq_paper from the source-q identification. -/
theorem qPilotLogVolume_eq_paper_of_sourceQ
    (h : ConcreteSourceQIdentification (I := I) C3) :
    O.qPilotLogVolume = paperQPilotLogVolume C3 :=
  (qPilotLogVolume_eq_paper_iff_sourceQ O C3).mpr h

/-- Conditional PaperXiFSourceLink with qPilotLogVolume_eq_paper filled; the
link fields remain explicit hypotheses. -/
noncomputable def paperXiFSourceLinkOfSourceQ
    (hsource : ConcreteSourceQIdentification (I := I) C3)
    (hident :
      O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (link_identification : Prop)
    (link_implies_inclusion : link_identification →
      O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume) :
    PaperXiFSourceLink O P C3 where
  source_identifications := hident
  qPilotLogVolume_eq_paper :=
    qPilotLogVolume_eq_paper_of_sourceQ O C3 hsource
  link_identification := link_identification
  link_implies_inclusion := link_implies_inclusion

end LeanFormal.IUT.XiFPaper.S674SourceQIdentificationPackageActual
end