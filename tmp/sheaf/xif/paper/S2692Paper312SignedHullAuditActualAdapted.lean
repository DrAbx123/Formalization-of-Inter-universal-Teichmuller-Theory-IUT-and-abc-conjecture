import tmp.sheaf.xif.paper.OrigXiFPaperQPilotObjectActual
import tmp.sheaf.xif.paper.OrigXiFPaperSignedHullActual
import tmp.sheaf.xif.paper.ActualPaperThetaLinkActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.OrigXiF
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaperThetaHull
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S2692Paper312SignedHullAuditActualAdapted

universe u
variable {l : PrimeGeFive} {X : Type u} [TopologicalSpace X]
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))

/-- The actual q-pilot scalar of the concrete paper q-pilot object. -/
noncomputable def S2692QPilotScalar : Real :=
  (origXiFPaperQPilotObjectActual (l := l) I).qPilotLogVolume

theorem S2692QPilotScalar_eq :
    S2692QPilotScalar (l := l) I = -OrigXiFPaperBadQAbsLog I.initial :=
  origXiFPaperQPilotObjectActual_qPilotLogVolume (l := l) I

theorem S2692QPilotScalar_eq_sourceBadQAbsLog :
    S2692QPilotScalar (l := l) I = -sourceBadQAbsLog I.initial :=
  origXiFPaperQPilotObjectActual_qPilotLogVolume (l := l) I

/-- The exact data still missing on the paper signed-hull side: an actual
`ActualThetaHull` with its IQ-carrier realization, a `SignedHullLogActual`
determinant, and the procession-normalization field, packaged as
`OrigXiFPaperSignedHullData`. -/
def S2692SignedHullDataMissing : Prop :=
  Nonempty (OrigXiFPaperSignedHullData X l)

/-- The actual signed hull constructed from the missing data. -/
noncomputable def S2692PaperSignedHull
    (D : OrigXiFPaperSignedHullData X l) :
    PaperSignedHull X (SignedLabel l.value) :=
  OrigXiFPaperSignedHull D

theorem S2692PaperSignedHull_signedHullLogVolume
    (D : OrigXiFPaperSignedHullData X l) :
    (S2692PaperSignedHull D).signedHullLogVolume =
      OrigXiFSignedThetaHullLogVolume D :=
  OrigXiFPaperSignedHull_signedHullLogVolume D

/-- The paper 3.12 (xi-f) q-pilot signed-hull comparison, stated as the actual
ray obligation of `ThetaLinkActual`. -/
def S2692Paper312Comparison
    (D : OrigXiFPaperSignedHullData X l) : Prop :=
  OrigXiFThetaLinkRayObligation D (S2692QPilotScalar (l := l) I)

theorem S2692Paper312Comparison_iff
    (D : OrigXiFPaperSignedHullData X l) :
    S2692Paper312Comparison (l := l) I D ↔
      S2692QPilotScalar (l := l) I ≤ OrigXiFSignedThetaHullLogVolume D :=
  OrigXiFThetaLinkRayObligation_iff D (S2692QPilotScalar (l := l) I)

theorem S2692Paper312Comparison_of_neg_abs_le
    (D : OrigXiFPaperSignedHullData X l) {qParameter : Real}
    (hq : S2692QPilotScalar (l := l) I = -|Real.log qParameter|)
    (h : -|Real.log qParameter| ≤ OrigXiFSignedThetaHullLogVolume D) :
    S2692Paper312Comparison (l := l) I D := by
  rw [S2692Paper312Comparison_iff, hq]
  exact h

/-- The carrier-realization field of an actual theta hull: this is the exact
literal `IQ(S+_{j+1}; n,circ D^vdash_{vQ})` realization obligation. -/
def S2692ThetaHullCarrierRealization (T : ActualThetaHull X l) : Prop :=
  T.paper_IQCarrier_realization

#check S2692QPilotScalar_eq
#check S2692PaperSignedHull
#check S2692Paper312Comparison_iff
#check S2692ThetaHullCarrierRealization

end LeanFormal.IUT.XiFPaper.S2692Paper312SignedHullAuditActualAdapted
end
