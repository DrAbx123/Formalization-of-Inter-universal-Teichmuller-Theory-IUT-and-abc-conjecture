import tmp.sheaf.xif.paper.S630ActualQPilotXiFLinkAudit
import tmp.sheaf.xif.paper.ThetaLinkFromSource
/-! # S637: construct the actual bridge and connect ThetaLinkFromSource
Explicit parameters: source_q identification, source-identification Prop with
its proof, and the actual ThetaLinkFromSource.actualThetaLink.  The bridge
does not fake link_identification/link_implies_inclusion. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S637ActualPaperXiFBridgeActualAdapted
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ThetaLinkFromSource
open LeanFormal.IUT.XiFPaper.S630ActualQPilotXiFLinkAudit
universe ua uv upi umon ui uC3 uD3 uM uP uX uLabel
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (O : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP} (I := I))
variable (P : PaperSignedHull X label)
/-- The actual Theta link from the actual carriers. -/
noncomputable def actualThetaLinkOfBridge :
    ActualThetaLink O P :=
  actualThetaLink O P
Theorem actualThetaLinkOfBridge_identification :
    (actualThetaLinkOfBridge O P).link_identification =
      thetaSourceComparison O P := rfl
/-- Construct the S630 bridge under explicit source-q and source-identification
parameters.  The link fields are the actual Theta-link fields, not True. -/
noncomputable def actualPaperXiFLinkBridge
    (hq : ActualToLegacySourceQIdentification (I := I) O)
    (source_identifications : Prop) (hsource : source_identifications) :
    ActualPaperXiFLinkBridge (I := I) O where
  source_q_identification := hq
  source_identifications_required := source_identifications
  link_identification := (actualThetaLinkOfBridge O P).link_identification
  link_implies_inclusion :=
    ∀ h : thetaSourceComparison O P,
      O.signedQPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume
/-- The bridge's link_identification is the actual source comparison. -/
theorem actualPaperXiFLinkBridge_link_identification
    (hq : ActualToLegacySourceQIdentification (I := I) O)
    (source_identifications : Prop) (hsource : source_identifications) :
    (actualPaperXiFLinkBridge O P hq source_identifications hsource).link_identification =
      thetaSourceComparison O P := rfl
/-- The bridge's link_implies_inclusion field is inhabited by the actual
Theta-link implication; this proves the field without replacing it by True. -/
theorem actualPaperXiFLinkBridge_link_implies_inclusion
    (hq : ActualToLegacySourceQIdentification (I := I) O)
    (source_identifications : Prop) (hsource : source_identifications)
    (h : thetaSourceComparison O P) :
    O.signedQPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume :=
  (actualThetaLinkOfBridge O P).link_implies_inclusion h
theorem actualPaperXiFLinkBridge_required
    (hq : ActualToLegacySourceQIdentification (I := I) O)
    (source_identifications : Prop) (hsource : source_identifications) :
    ActualPaperXiFLinkBridgeRequired (I := I) O :=
  ⟨actualPaperXiFLinkBridge O P hq source_identifications hsource⟩
end LeanFormal.IUT.XiFPaper.S637ActualPaperXiFBridgeActualAdapted
