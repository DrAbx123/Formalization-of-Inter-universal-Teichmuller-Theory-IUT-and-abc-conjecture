import tmp.sheaf.xif.paper.S1032CanonicalLinkInstantiationActual
import tmp.sheaf.xif.paper.ThetaLinkFromSource

/-! # S1033: audit of the exact hlink thetaSourceComparison

hlink = thetaSourceComparison (s1009CanonicalOa I C1 C2 C3) P
      = P.procession.average ≤ -Oa.signedQPilotLogVolume.

ThetaLinkFromSource defines this comparison as a Prop and provides only the
implication to hull-ray membership.  No actual proof of the comparison exists
in the tree; it is the paper source comparison (Cor 3.12 core input), not a
consequence of the constructed hull inequalities for an arbitrary P.
This file records the exact minimum and the actual equivalence with the
hull-ray membership form.  No fake proof is added. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1033ThetaSourceComparisonAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ThetaLinkFromSource
open LeanFormal.IUT.XiFPaper.S1032CanonicalLinkInstantiationActual
open LeanFormal.IUT.XiFPaper.S1009HQHC3Actual

universe uX uLabel uC3 uD3

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]
variable (P : PaperSignedHull X label)
variable (C1 : SourceInputBinding I)
variable (C2 : SourceLogKummerData I C1)
variable (C3 : SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) I)

/-- Exact hlink proposition for the canonical Oa. -/
def S1033ThetaSourceComparisonRequired : Prop :=
  thetaSourceComparison (s1009CanonicalOa (l := l) I C1 C2 C3) P

/-- Actual equivalence: the source comparison is exactly the hull-ray
membership of the signed q-pilot volume. -/
theorem s1033ThetaSourceComparison_iff_membership :
    S1033ThetaSourceComparisonRequired (l := l) I P C1 C2 C3 ↔
      (s1009CanonicalOa (l := l) I C1 C2 C3).signedQPilotLogVolume ∈
        hullLogVolumeRay P.signedHullLogVolume := by
  unfold S1033ThetaSourceComparisonRequired thetaSourceComparison
  rw [mem_hullLogVolumeRay_iff, P.signedHullLogVolume_eq_neg_average]
  constructor <;> intro h <;> linarith

/-- The actual membership direction is available from the comparison (already
in ThetaLinkFromSource). -/
theorem s1033Membership_of_thetaSourceComparison
    (h : S1033ThetaSourceComparisonRequired (l := l) I P C1 C2 C3) :
    (s1009CanonicalOa (l := l) I C1 C2 C3).signedQPilotLogVolume ∈
      hullLogVolumeRay P.signedHullLogVolume :=
  (s1033ThetaSourceComparison_iff_membership (l := l) I P C1 C2 C3).mp h

/-- Exact minimal remaining comparison: the paper source comparison. -/
def S1033FinalComparisonRequired : Prop :=
  S1033ThetaSourceComparisonRequired (l := l) I P C1 C2 C3

end LeanFormal.IUT.XiFPaper.S1033ThetaSourceComparisonAuditActual

end
