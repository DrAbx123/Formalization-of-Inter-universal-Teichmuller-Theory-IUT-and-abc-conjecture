import tmp.sheaf.xif.paper.ThetaLinkFromSource
import tmp.sheaf.n8.closure.C3Actual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

/-!
# PaperXiFSourceLink from the actual Theta-link and signed hull membership

This file constructs the actual paper source-link fields from:

* an ActualThetaLink L of ThetaLinkFromSource, whose link_identification is the
  concrete source comparison and whose link_implies_inclusion is the actual
  signed-hull membership theorem;
* the source identifications of the old paper q-pilot object O;
* the actual paper q-pilot scalar identification
  O.qPilotLogVolume = paperQPilotLogVolume C3;
* the scalar equality connecting the old q-pilot object to the actual q-pilot
  object Oa: O.qPilotLogVolume = Oa.signedQPilotLogVolume.

The resulting PaperXiFSourceLink has

  link_identification := L.link_identification
  link_implies_inclusion := transfer of L.link_implies_inclusion along the
    scalar equality.

Thus link_identification is not True and no inequality is asserted: the
comparison remains the concrete source comparison of L. The construction is
conditional only on the explicit source-identification and scalar-equality
proofs supplied as arguments.

No donor structure, no Missing-only structure, no True/PUnit, axiom, or sorry
is used.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.PaperXiFSourceLinkActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ThetaLinkFromSource

universe ua uv upi umon ui uL uC uG uX uLabel uC3 uD3 uM uP

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]

variable {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
variable {P : PaperSignedHull X label}
variable {C3 : SourcePilotRegionData I}
variable {Oa : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP} (l := l) (V := V) (I := I)}

/-- Construct the actual PaperXiFSourceLink from an actual Theta-link and the
old/actual q-pilot scalar connection. -/
def sourceLinkOfActualThetaLink
    (L : ActualThetaLink Oa P)
    (hsrc :
      O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hq : O.qPilotLogVolume = paperQPilotLogVolume C3)
    (hEq : O.qPilotLogVolume = Oa.signedQPilotLogVolume) :
    PaperXiFSourceLink O P C3 where
  source_identifications := hsrc
  qPilotLogVolume_eq_paper := hq
  link_identification := L.link_identification
  link_implies_inclusion := by
    intro h
    have hmem := L.link_implies_inclusion h
    rw [← hEq] at hmem
    exact hmem

/-- The link identification of the constructed source link is exactly the
actual Theta-link identification. -/
theorem sourceLinkOfActualThetaLink_identification
    (L : ActualThetaLink Oa P)
    (hsrc :
      O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hq : O.qPilotLogVolume = paperQPilotLogVolume C3)
    (hEq : O.qPilotLogVolume = Oa.signedQPilotLogVolume) :
    (sourceLinkOfActualThetaLink L hsrc hq hEq).link_identification =
      L.link_identification :=
  rfl

/-- The constructed source link's inclusion is the actual signed hull membership
transferred along the scalar equality. -/
theorem sourceLinkOfActualThetaLink_inclusion
    (L : ActualThetaLink Oa P)
    (hsrc :
      O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hq : O.qPilotLogVolume = paperQPilotLogVolume C3)
    (hEq : O.qPilotLogVolume = Oa.signedQPilotLogVolume)
    (hlink : L.link_identification) :
    O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume :=
  (sourceLinkOfActualThetaLink L hsrc hq hEq).link_implies_inclusion hlink

/-- Actual PaperXiFInclusion from an actual Theta-link whose identification
holds and the scalar equality fields. -/
def paperXiFInclusionOfActualThetaLink
    (L : ActualThetaLink Oa P)
    (hsrc :
      O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hq : O.qPilotLogVolume = paperQPilotLogVolume C3)
    (hEq : O.qPilotLogVolume = Oa.signedQPilotLogVolume)
    (hlink : L.link_identification) :
    PaperXiFInclusion O P C3 where
  link := sourceLinkOfActualThetaLink L hsrc hq hEq
  link_holds := hlink

/-- The actual paper xi-f membership from the constructed link. -/
theorem paperXiF_membership_of_actualThetaLink
    (L : ActualThetaLink Oa P)
    (hsrc :
      O.paper_strip_identification ∧
      O.paper_lineBundle_identification ∧
      O.paper_logKummer_identification ∧
      O.paper_qPilot_log_identification)
    (hq : O.qPilotLogVolume = paperQPilotLogVolume C3)
    (hEq : O.qPilotLogVolume = Oa.signedQPilotLogVolume)
    (hlink : L.link_identification) :
    O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume :=
  (paperXiFInclusionOfActualThetaLink L hsrc hq hEq hlink).qPilot_mem_ray

end LeanFormal.IUT.XiFPaper.PaperXiFSourceLinkActual

end
