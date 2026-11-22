import tmp.sheaf.xif.paper.PaperXiFSourceLinkActual
import tmp.sheaf.xif.PaperAssembly
import tmp.sheaf.xif.paper.ThetaLinkFromSource

/-! # S628: PaperXiFSourceLink construction from ConcreteSourceQIdentification
and thetaSourceComparison

Given the source-q identification and the paper theta/q comparison, build the
four PaperXiFSourceLink fields, PaperXiFInclusion, and the certificate chain.
No fake inequality. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S628PaperXiFSourceLinkConstructionActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ThetaLinkFromSource
open LeanFormal.IUT.XiFPaper.PaperXiFSourceLinkActual

universe ua uv upi umon ui uL uC uG uX uLabel uC3 uD3 uM uP

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
variable {P : PaperSignedHull X label}
variable {C3 : SourcePilotRegionData (l := l) (V := V) I}
variable {Oa : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP} (l := l) (V := V) (I := I)}

/-- Exact source-q identification: source bad-q scalar equals C3 local log. -/
def ConcreteSourceQIdentification
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Prop :=
  sourceQPilotSignedLog I.initial = localSignedLog C3.q

/-- The q-pilot scalar equals the paper q scalar from the source-q
identification. -/
theorem qPilotLogVolume_eq_paper
    (hq : ConcreteSourceQIdentification I C3)
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip) :
    O.qPilotLogVolume = paperQPilotLogVolume C3 := by
  rw [O.qPilotLogVolume_eq, hq, paperQPilotLogVolume_eq_log_norm]
  rfl

/-- The old q-pilot scalar equals the actual q-pilot scalar. -/
theorem qPilotLogVolume_eq_actual
    (hq : ConcreteSourceQIdentification I C3)
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (Oa : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP} (l := l) (V := V) (I := I))
    (hC3 : Oa.line.C3 = C3) :
    O.qPilotLogVolume = Oa.signedQPilotLogVolume := by
  rw [O.qPilotLogVolume_eq, hq, hC3]
  rfl

/-- Four-field PaperXiFSourceLink construction. -/
noncomputable def s628PaperXiFSourceLink
    (hq : ConcreteSourceQIdentification I C3)
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (Oa : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP} (l := l) (V := V) (I := I))
    (hC3 : Oa.line.C3 = C3)
    (hsrc : O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hcomp : thetaSourceComparison Oa P) :
    PaperXiFSourceLink O P C3 :=
  sourceLinkOfActualThetaLink (actualThetaLink Oa P) hsrc
    (qPilotLogVolume_eq_paper (I := I) hq O)
    (qPilotLogVolume_eq_actual (I := I) hq O Oa hC3)

/-- PaperXiFInclusion from the constructed link plus the comparison proof. -/
noncomputable def s628PaperXiFInclusion
    (hq : ConcreteSourceQIdentification I C3)
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (Oa : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP} (l := l) (V := V) (I := I))
    (hC3 : Oa.line.C3 = C3)
    (hsrc : O.paper_strip_identification ∧ O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧ O.paper_qPilot_log_identification)
    (hcomp : thetaSourceComparison Oa P) :
    PaperXiFInclusion O P C3 :=
  paperXiFInclusionOfActualThetaLink (actualThetaLink Oa P) hsrc
    (qPilotLogVolume_eq_paper (I := I) hq O)
    (qPilotLogVolume_eq_actual (I := I) hq O Oa hC3)
    (by simpa [actualThetaLink] using hcomp)

/-- The paper q-pilot vs signed hull inequality from the constructed inclusion. -/
theorem s628qPilot_le_signedHull
    (hq : ConcreteSourceQIdentification I C3)
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (Oa : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP} (l := l) (V := V) (I := I))
    (hC3 : Oa.line.C3 = C3)
    (hsrc : O.paper_strip_identification ∧ O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧ O.paper_qPilot_log_identification)
    (hcomp : thetaSourceComparison Oa P) :
    O.qPilotLogVolume ≤ P.signedHullLogVolume :=
  (s628PaperXiFInclusion (I := I) hq O Oa hC3 hsrc hcomp).qPilot_le_signedHull

/-- Certificate chain: the paper certificate q <= theta conclusion. -/
theorem s628Certificate_q_le_theta
    [Nonempty label]
    (hq : ConcreteSourceQIdentification I C3)
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (Oa : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP} (l := l) (V := V) (I := I))
    (hC3 : Oa.line.C3 = C3)
    (hsrc : O.paper_strip_identification ∧ O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧ O.paper_qPilot_log_identification)
    (hcomp : thetaSourceComparison Oa P) :
    (paperCertificate (I := paperXiFInput
      (s628PaperXiFInclusion (I := I) hq O Oa hC3 hsrc hcomp))).qSigned ≤
      (paperCertificate (I := paperXiFInput
        (s628PaperXiFInclusion (I := I) hq O Oa hC3 hsrc hcomp))).thetaSigned :=
  paperCertificate_q_le_theta
    (I := paperXiFInput
      (s628PaperXiFInclusion (I := I) hq O Oa hC3 hsrc hcomp))

end LeanFormal.IUT.XiFPaper.S628PaperXiFSourceLinkConstructionActualAdapted

end
