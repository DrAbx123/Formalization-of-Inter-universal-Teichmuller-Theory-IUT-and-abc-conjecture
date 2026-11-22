import tmp.sheaf.xif.paper.PaperXiFSourceLinkActual
import tmp.sheaf.xif.PaperAssembly
import tmp.sheaf.xif.paper.S627ThetaSourceComparisonActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S634PaperXiFConditionalCor312Actual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ThetaLinkFromSource
open LeanFormal.IUT.XiFPaper.PaperXiFSourceLinkActual
open LeanFormal.IUT.XiFPaper.S627ThetaSourceComparisonActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume

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

theorem qPilotLogVolume_eq_paper
    (hq : ConcreteSourceQIdentification I C3)
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip) :
    O.qPilotLogVolume = paperQPilotLogVolume C3 := by
  rw [O.qPilotLogVolume_eq, hq, paperQPilotLogVolume_eq_log_norm]
  rfl

/-- Conditional PaperXiFSourceLink from the source-q identification and the
explicit missing paper xi-f comparison. -/
noncomputable def s634PaperXiFSourceLink
    (hq : ConcreteSourceQIdentification I C3)
    (hgap : MissingPaperXiFComparison Oa P)
    (hsrc : O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hC3 : Oa.line.C3 = C3)
    (hEq : O.qPilotLogVolume = Oa.signedQPilotLogVolume) :
    PaperXiFSourceLink O P C3 :=
  let L := actualThetaLink Oa P
  let hcomp : thetaSourceComparison Oa P :=
    (thetaSourceComparison_iff_gap Oa P).mpr hgap
  have hlink : L.link_identification := by
    rw [actualThetaLink_link_identification]
    exact hcomp
  sourceLinkOfActualThetaLink L hsrc
    (qPilotLogVolume_eq_paper (I := I) hq O) hEq

/-- Conditional PaperXiFInclusion from the same parameters. -/
noncomputable def s634PaperXiFInclusion
    (hq : ConcreteSourceQIdentification I C3)
    (hgap : MissingPaperXiFComparison Oa P)
    (hsrc : O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hC3 : Oa.line.C3 = C3)
    (hEq : O.qPilotLogVolume = Oa.signedQPilotLogVolume) :
    PaperXiFInclusion O P C3 :=
  let L := actualThetaLink Oa P
  let hcomp : thetaSourceComparison Oa P :=
    (thetaSourceComparison_iff_gap Oa P).mpr hgap
  have hlink : L.link_identification := by
    rw [actualThetaLink_link_identification]
    exact hcomp
  paperXiFInclusionOfActualThetaLink L hsrc
    (qPilotLogVolume_eq_paper (I := I) hq O) hEq hlink

/-- Conditional paperCertificate Cor312Conclusion, with finite IPL/SHE/APT
evidence as an explicit parameter. -/
theorem s634Cor312Conclusion
    [Nonempty label]
    (hq : ConcreteSourceQIdentification I C3)
    (hgap : MissingPaperXiFComparison Oa P)
    (hsrc : O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hC3 : Oa.line.C3 = C3)
    (hEq : O.qPilotLogVolume = Oa.signedQPilotLogVolume)
    (links : FiniteStepXILinkEvidence
      (paperCertificate (I := paperXiFInput
        (s634PaperXiFInclusion (I := I) hq hgap hsrc hC3 hEq))).toStepXIFiniteCertificate) :
    Cor312Conclusion
      ((paperCertificate (I := paperXiFInput
        (s634PaperXiFInclusion (I := I) hq hgap hsrc hC3 hEq))).toContract
        (paperSignedLinkEvidence
          (I := paperXiFInput
            (s634PaperXiFInclusion (I := I) hq hgap hsrc hC3 hEq)) links)) :=
  paperCor312Conclusion
    (I := paperXiFInput (s634PaperXiFInclusion (I := I) hq hgap hsrc hC3 hEq)) links

end LeanFormal.IUT.XiFPaper.S634PaperXiFConditionalCor312Actual

end
