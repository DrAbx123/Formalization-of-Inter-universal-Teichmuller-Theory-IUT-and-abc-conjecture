import tmp.sheaf.xif.paper.S1036GlobalQPilotObjectAuditActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import tmp.sheaf.xif.paper.S994FiniteCarrierCor312Actual
import tmp.sheaf.xif.paper.S919GlobalWeightedInequalityActual

/-! # S1037: paper Cor3.12 qPilot object is global, not local

PaperLevelXiFTargetProofActual.globalQPilotLog is
  sum_b nativeBadLocalWeight T b * perBQPilotLog T b,
a global Bad-place weighted sum.  The single C3.q is a local finite-place q and
is not the paper qPilot object.

Therefore the correct sourceQ/hQ is a GLOBAL bridge
  globalQPilotLog T = weightedPaperV T (s994VR T In),
which reduces pointwise to perBQPilotLog T b = s994VR T In b.
The corrected bridge and conditional comparison are actual; the pointwise
identification and hull magnitude identification remain exact.  No fake. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1037GlobalQPilotAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.S1025S994FiniteInputActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open MeasureTheory

universe uX uLabel

variable {l : PrimeGeFive}
variable {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]
variable (P : PaperSignedHull X label)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- The paper qPilot object is the global Bad-place weighted sum. -/
theorem s1037GlobalQPilotLog_eq_weighted :
    globalQPilotLog (l := l) T =
      weightedPaperV (l := l) T (perBQPilotLog (l := l) T) := rfl

/-- Corrected global sourceQ/hQ bridge. -/
structure S1037CorrectedBridge (In : S994FiniteInput T) where
  perBQPilot_eq : ∀ b : Bad (nativePlaceSelection T),
    perBQPilotLog (l := l) T b = s994VR (l := l) T In b
  hullMagnitude_eq :
    P.procession.average =
      -weightedPaperV (l := l) T (s994VS (l := l) T In)

/-- The pointwise per-b identification implies the global qPilot bridge. -/
theorem s1037GlobalQPilot_eq_weightedVR_of_perB
    (In : S994FiniteInput T)
    (h : ∀ b : Bad (nativePlaceSelection T),
      perBQPilotLog (l := l) T b = s994VR (l := l) T In b) :
    globalQPilotLog (l := l) T =
      weightedPaperV (l := l) T (s994VR (l := l) T In) := by
  unfold globalQPilotLog weightedPaperV
  apply Finset.sum_congr rfl
  intro b _
  rw [h b]

/-- Corrected global comparison: P.average ≤ -global qPilot log. -/
theorem s1037GlobalComparison_of_bridge
    (In : S994FiniteInput T)
    (hb : S1037CorrectedBridge (l := l) P T In) :
    P.procession.average ≤ -globalQPilotLog (l := l) T := by
  have hglobal := s1037GlobalQPilot_eq_weightedVR_of_perB (l := l) T In hb.perBQPilot_eq
  rw [hb.hullMagnitude_eq]
  rw [hglobal]
  have h := s994GlobalWeightedInequality (l := l) T In
  linarith

/-- Exact corrected bridge existence. -/
def S1037CorrectedBridgeRequired : Prop :=
  ∃ In : S994FiniteInput T,
    Nonempty (S1037CorrectedBridge (l := l) P T In)

/-- Exact pointwise per-b qPilot identification (the reduced global sourceQ). -/
def S1037PerBQPilotIdentificationRequired : Prop :=
  ∃ In : S994FiniteInput T,
    ∀ b : Bad (nativePlaceSelection T),
      perBQPilotLog (l := l) T b = s994VR (l := l) T In b

end LeanFormal.IUT.XiFPaper.S1037GlobalQPilotAuditActual

end
