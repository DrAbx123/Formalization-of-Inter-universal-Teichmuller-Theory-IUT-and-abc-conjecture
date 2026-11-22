import tmp.sheaf.xif.paper.S2040ActualThetaLink312

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S2040FourQPilotAuditActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ThetaLink
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2040ActualThetaLink312

universe ua uv upi umon uL uC uG uX ulab
variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, 0} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip.{umon, uv, upi} V}
variable {X : Type uX} {label : Type ulab} [Fintype label]

/-- The four paper q-pilot identifications as the actual conjunction. -/
abbrev S2040FourQPilotIdentifications
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip) : Prop :=
  thetaLinkQPilotPaperIdentifications O

/-- Exact decomposition of the four identifications (definitional). -/
theorem s2040FourQPilotIdentifications_iff
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip) :
    S2040FourQPilotIdentifications O ↔
      O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification :=
  Iff.rfl

/-- Exact construction obligations of the S2038 paper O interface.  The four
identification field is not asserted; q_lt_one is the explicit contracting
condition on the actual one-column q. -/
structure S2040PaperOConstructionRequired
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip) where
  q : Real
  q_eq_source : q = I.oneColumnQAtZero
  q_pos : 0 < q
  q_lt_one : q < 1
  qPilotStrip : FPrimeStrip V
  qPilotStrip_eq : qPilotStrip = I.primeStripAt 1 0
  thetaPilotStrip : FPrimeStrip V
  thetaPilotStrip_eq : thetaPilotStrip = I.primeStripAt 0 0
  paperO_identifications : S2040FourQPilotIdentifications O

/-- Exact displacement obligation: the S2040 log-theta-lattice data. -/
abbrev S2040DisplacementRequired
    (Opaper : S2038PaperOActual (I := I) (G := G) (envStrip := envStrip)
      (Label := Label) (Choice := Choice) (l := l) (V := V) O) : Type _ :=
  S2040ThetaLinkDisplacement Opaper

/-- Exact q-pilot log identification component. -/
def S2040QPilotLogRequired
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (Opaper : S2038PaperOActual (I := I) (G := G) (envStrip := envStrip)
      (Label := Label) (Choice := Choice) (l := l) (V := V) O) : Prop :=
  S2040QPilotLogIdentification O Opaper

/-- Exact hull normalization component. -/
def S2040HullNormalizationRequired
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (Opaper : S2038PaperOActual (I := I) (G := G) (envStrip := envStrip)
      (Label := Label) (Choice := Choice) (l := l) (V := V) O)
    (P : PaperSignedHull X label)
    (D : S2040ThetaLinkDisplacement Opaper) : Prop :=
  S2040HullNormalization Opaper P D

end LeanFormal.IUT.XiFPaper.S2040FourQPilotAuditActual
end