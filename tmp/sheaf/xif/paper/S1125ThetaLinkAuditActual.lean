import tmp.sheaf.xif.paper.ThetaLinkActual
import tmp.sheaf.xif.paper.ThetaLinkLogKummerActual
import tmp.sheaf.xif.PaperXiFInclusion
import tmp.sheaf.xif.paper.ConcreteSourceComparisonActual
import tmp.sheaf.xif.paper.Theorem311KummerPacketIsoGapActual
/-! # S1125: Theta-link audit
Reuse audit of the five existing Theta-link files.  No object is duplicated.
The gluing isomorphism is not present in these files; the exact minimum is the
existing global Kummer tensor-packet iso gap. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S1125ThetaLinkAuditActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ThetaLink
open LeanFormal.IUT.XiFPaper.Theorem311KummerPacketIsoGapActual
open LeanFormal.IUT.Theorem311Source.ConcreteSourceComparisonActual
universe ua upi umon ui uX uLabel
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0,0,0,0,0} l (FinitePrimePlace 2 7))
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (P : PaperSignedHull X label)
/-- Link identification is exactly the concrete source comparison proposition. -/
theorem s1125_link_identification_exact :
    (concreteSourceLink (l := l) I P).link_identification =
      concreteSourceComparison (l := l) I P := rfl
/-- The link implication is the actual proved ray membership. -/
theorem s1125_link_implies_inclusion_actual
    (h : (concreteSourceLink (l := l) I P).link_identification) :
    concreteQLogVolume (l := l) I ∈
      hullLogVolumeRay P.signedHullLogVolume :=
  concreteSourceLink_membership (l := l) I P h
/-- No gluing isomorphism is constructed in the Theta-link files; the exact
minimum is the global Kummer tensor-packet iso gap. -/
def S1125GluingExactMinimum : Prop :=
  GlobalKummerTensorPacketIsoRequired
end LeanFormal.IUT.XiFPaper.S1125ThetaLinkAuditActual
