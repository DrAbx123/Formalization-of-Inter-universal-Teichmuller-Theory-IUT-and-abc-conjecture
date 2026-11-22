import tmp.sheaf.xif.paper.S1037GlobalQPilotAuditActual
import tmp.sheaf.xif.paper.S1025S994FiniteInputActual

/-! # S1043: exact data of S1037CorrectedBridge

The corrected bridge has two independent components:
  (1) per-b perBQPilotLog T b = s994VR T In b;
  (2) P.procession.average = -weightedPaperV T (s994VS T In).
Both are exact data, not consequences of the definitions: perBQPilotLog uses
the classical c_norm region, while s994VR uses the paper qPilot region, and
P.average is an external hull quantity.  This file proves the equivalence with
the structure and the conditional actual construction; no fake equality. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1043CorrectedBridgeExactActual

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
open LeanFormal.IUT.XiFPaper.S1037GlobalQPilotAuditActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open LeanFormal.IUT.XiFPaper.S1025S994FiniteInputActual
open MeasureTheory

universe uX uLabel

variable {l : PrimeGeFive}
variable {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]
variable (P : PaperSignedHull X label)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (In : S994FiniteInput T)

/-- Exact per-b qPilot identification. -/
def S1043PerBQPilotExact : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    perBQPilotLog (l := l) T b = s994VR (l := l) T In b

/-- Exact hull-average identification. -/
def S1043HullAverageExact : Prop :=
  P.procession.average =
    -weightedPaperV (l := l) T (s994VS (l := l) T In)

/-- Exact data of the corrected bridge. -/
def S1043CorrectedBridgeExact : Prop :=
  S1043PerBQPilotExact (l := l) T In ∧
    S1043HullAverageExact (l := l) P T In

/-- Exact data constructs S1037CorrectedBridge. -/
noncomputable def s1043BridgeOfExact
    (h : S1043CorrectedBridgeExact (l := l) P T In) :
    S1037CorrectedBridge (l := l) P T In where
  perBQPilot_eq := h.1
  hullMagnitude_eq := h.2

/-- The corrected bridge is exactly the pair of exact equalities. -/
theorem s1043BridgeRequired_iff_exact :
    Nonempty (S1037CorrectedBridge (l := l) P T In) ↔
      S1043CorrectedBridgeExact (l := l) P T In := by
  constructor
  · rintro ⟨D⟩
    exact ⟨D.perBQPilot_eq, D.hullMagnitude_eq⟩
  · intro h
    exact ⟨s1043BridgeOfExact (l := l) P T In h⟩

/-- Conditional actual S1037 comparison from the exact data. -/
theorem s1043GlobalComparison_of_exact
    (h : S1043CorrectedBridgeExact (l := l) P T In) :
    P.procession.average ≤ -globalQPilotLog (l := l) T :=
  s1037GlobalComparison_of_bridge (l := l) P T In
    (s1043BridgeOfExact (l := l) P T In h)

end LeanFormal.IUT.XiFPaper.S1043CorrectedBridgeExactActual

end
