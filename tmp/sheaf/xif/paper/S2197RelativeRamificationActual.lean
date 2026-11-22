import tmp.sheaf.xif.paper.S2187QVPlaceUnramifiedActual
import tmp.sheaf.xif.paper.S2176RamificationE1Actual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.S2197RelativeRamificationActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2187QVPlaceUnramifiedActual
open LeanFormal.IUT.XiFPaper.S2176RamificationE1Actual
open LeanFormal.IUT.XiFPaper.S2040QVPlaceSplitActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
/-- The relative ramification index is Mathlib's global finite-place ramification
index. -/
theorem s2197_relativeRamification_eq_global :
    relativeRamificationIndex (k := ℚ) (qVFamTensorPlace T b) =
      (qVFamTensorPlace T b).maximalIdeal.asIdeal.ramificationIdx
        (NumberField.RingOfIntegers ℚ) := by
  exact relativeRamificationIndex_eq_ramificationIdx (k := ℚ) (K := T.arithmetic.F)
    (qVFamTensorPlace T b)
/-- Unramified is equivalent to the completion degree equalling the residue
degree. -/
theorem s2197_unramified_iff_completionDegree_eq_residue :
    S2040QVPlaceUnramifiedRequired T b ↔
      relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b) =
        relativeResidueDegree (k := ℚ) (qVFamTensorPlace T b) := by
  rw [s2187_unramified_iff_relativeRamificationIndex_one]
  constructor
  · intro he
    unfold relativeCompletionDegree
    rw [he, one_mul]
  · intro h
    unfold relativeCompletionDegree at h
    have hf : 0 < relativeResidueDegree (k := ℚ) (qVFamTensorPlace T b) :=
      Nat.pos_of_ne_zero
        (relativeResidueDegree_ne_zero (k := ℚ) (K := T.arithmetic.F) (qVFamTensorPlace T b))
    have h' : relativeRamificationIndex (k := ℚ) (qVFamTensorPlace T b) *
          relativeResidueDegree (k := ℚ) (qVFamTensorPlace T b) =
        1 * relativeResidueDegree (k := ℚ) (qVFamTensorPlace T b) := by
      simpa using h
    exact Nat.mul_right_cancel hf h'
/-- Exact missing numerical value of the relative ramification index. -/
def s2197RelativeRamificationValue : Prop :=
  relativeRamificationIndex (k := ℚ) (qVFamTensorPlace T b) = 1
/-- Exact missing completion-degree equality. -/
def s2197CompletionDegreeEq : Prop :=
  relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b) =
    relativeResidueDegree (k := ℚ) (qVFamTensorPlace T b)
/-- Exact missing global ramification index computation. -/
def s2197GlobalRamificationIdx : Prop :=
  (qVFamTensorPlace T b).maximalIdeal.asIdeal.ramificationIdx
    (NumberField.RingOfIntegers ℚ) = 1
/-- The carrier bridge remains unchanged and missing. -/
def s2197CompletionCarrierBridgeMissing : Prop :=
  s2176CompletionCarrierBridgeMissing (l := l) T b
#print axioms s2197_relativeRamification_eq_global
#print axioms s2197_unramified_iff_completionDegree_eq_residue
end LeanFormal.IUT.XiFPaper.S2197RelativeRamificationActual
end
