import tmp.sheaf.xif.paper.S2197RelativeRamificationActual
noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.S2201RamificationValueActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2197RelativeRamificationActual
open LeanFormal.IUT.XiFPaper.S2187QVPlaceUnramifiedActual
open LeanFormal.IUT.XiFPaper.S2176RamificationE1Actual
open LeanFormal.IUT.XiFPaper.S2040QVPlaceSplitActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
/-- The relative completion degree is e*f by definition. -/
theorem s2201_relativeCompletionDegree_eq_mul :
    relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b) =
      relativeRamificationIndex (k := ℚ) (qVFamTensorPlace T b) *
        relativeResidueDegree (k := ℚ) (qVFamTensorPlace T b) := rfl
/-- The relative ramification index divides the relative completion degree. -/
theorem s2201_relativeRamification_dvd_completionDegree :
    relativeRamificationIndex (k := ℚ) (qVFamTensorPlace T b) ∣
      relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b) := by
  rw [s2201_relativeCompletionDegree_eq_mul]
  exact Nat.dvd_mul_right _ _
/-- Unramified is exactly the completion degree/residue degree equality. -/
theorem s2201_unramified_iff_completionDegree_eq_residue :
    S2040QVPlaceUnramifiedRequired T b ↔
      relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b) =
        relativeResidueDegree (k := ℚ) (qVFamTensorPlace T b) :=
  s2197_unramified_iff_completionDegree_eq_residue T b
/-- Exact missing numerical value: the global ramification index is one. -/
def s2201RamificationValueOne : Prop :=
  (qVFamTensorPlace T b).maximalIdeal.asIdeal.ramificationIdx
    (NumberField.RingOfIntegers ℚ) = 1
/-- Exact missing completion-degree equality. -/
def s2201CompletionDegreeEq : Prop :=
  relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b) =
    relativeResidueDegree (k := ℚ) (qVFamTensorPlace T b)
/-- Exact missing source arithmetic: the residue degree equals the completion
degree, equivalently e=1. -/
def s2201QVFamRamificationData : Prop :=
  s2201CompletionDegreeEq (l := l) T b
/-- Root coefficient carrier bridge unchanged. -/
def s2201CompletionCarrierBridgeMissing : Prop :=
  s2176CompletionCarrierBridgeMissing (l := l) T b
#print axioms s2201_relativeCompletionDegree_eq_mul
#print axioms s2201_relativeRamification_dvd_completionDegree
#print axioms s2201_unramified_iff_completionDegree_eq_residue
end LeanFormal.IUT.XiFPaper.S2201RamificationValueActual
end
