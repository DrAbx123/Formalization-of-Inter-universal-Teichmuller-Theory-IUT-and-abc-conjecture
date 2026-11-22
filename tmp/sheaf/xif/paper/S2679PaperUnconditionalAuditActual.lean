import tmp.sheaf.xif.paper.PaperXiFUnconditional
import tmp.sheaf.xif.paper.IPLAPTDataActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S2679PaperUnconditionalAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.IPLAPTDataActual
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume

universe ua uv upi umon ui uL uC uG uX uLabel

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]

/-- Actual self Theta-link data: the IPL factorization and Kummer-evaluation
two-path equality are the actual theorems of IPLAPTDataActual. -/
noncomputable def S2679ThetaLink :
    PaperThetaLinkData (G := SelfGroup envStrip)
      (intermediateStrip := envStrip) (gauStrip := envStrip)
      (envStrip := envStrip) (coricEnvStrip := envStrip)
      (qPilotStrip := envStrip)
      (upperLeft := envStrip) (upperRight := envStrip)
      (lowerLeft := envStrip) (lowerRight := envStrip) where
  ipl := selfIplActual envStrip
  kummerEvaluation := selfKummerEvaluationActual envStrip

/-- Minimal conditional assembly of PaperUnconditionalData.

Only three source fields are assumed:
* the four paper q-pilot identifications of O;
* the q-pilot log normalization equality O.qPilotLogVolume = paperQPilotLogVolume C3;
* a link identification proposition together with a proof and its implication to
  the hull ray.

The thetaLink field is actual (S2679ThetaLink), not an assumption. -/
noncomputable def S2679PaperUnconditionalData_conditional
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I
      (SelfGroup envStrip) envStrip)
    (P : PaperSignedHull X label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (hsource : thetaLinkQPilotPaperIdentifications O)
    (hq : O.qPilotLogVolume = paperQPilotLogVolume C3)
    (hlink : Prop) (hlink_holds : hlink)
    (himpl : hlink → O.qPilotLogVolume ∈
      hullLogVolumeRay P.signedHullLogVolume) :
    PaperUnconditionalData (label := label) (G := SelfGroup envStrip) envStrip
      O P C3 where
  sourceLink := {
    source_identifications := hsource
    qPilotLogVolume_eq_paper := hq
    link_identification := hlink
    link_implies_inclusion := himpl }
  sourceLink_holds := hlink_holds
  thetaLink := S2679ThetaLink (envStrip := envStrip)

#check S2679ThetaLink
#check S2679PaperUnconditionalData_conditional
#print axioms S2679ThetaLink
#print axioms S2679PaperUnconditionalData_conditional

end LeanFormal.IUT.XiFPaper.S2679PaperUnconditionalAuditActual
end
