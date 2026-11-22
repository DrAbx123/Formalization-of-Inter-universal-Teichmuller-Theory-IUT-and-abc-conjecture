import tmp.sheaf.xif.paper.S1052PaperQParameterCardActual
import tmp.sheaf.xif.paper.W6ActualPilotMonodromyActual
import tmp.sheaf.xif.paper.S919GlobalWeightedInequalityActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
/-! # S1059: negative paper global qPilot from per-b negativity
Per-b paper qPilot logs s994VR are the exact negativity input.  With nonnegative
native weights, positive at each bad place, and nonempty bad places, the
weighted sum is strictly negative. -/
noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
namespace LeanFormal.IUT.XiFPaper.S1059PaperGlobalSignActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.S1050PerBQPilotCoefficientAuditActual
open LeanFormal.IUT.XiFPaper.S1051PaperGlobalFinalActual
open LeanFormal.IUT.XiFPaper.S1052PaperQParameterCardActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.W6ActualPilotMonodromyActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
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
variable (In : S994FiniteInput T)
/-- Exact per-b negativity input. -/
def S1059PerBVRNegative : Prop :=
  ∀ b : Bad (nativePlaceSelection T), s994VR (l := l) T In b < 0
/-- Nonempty bad places, as the index-nonempty input. -/
def S1059NonemptyBad : Prop :=
  Nonempty (Bad (nativePlaceSelection T))
theorem s1059PaperGlobal_neg
    (hVR : S1059PerBVRNegative (l := l) T In)
    (hne : S1059NonemptyBad (l := l) T) :
    s1050PaperGlobalQPilotLog (l := l) T In < 0 := by
  unfold s1050PaperGlobalQPilotLog weightedPaperV
  obtain ⟨b0⟩ := hne
  have hsum := Finset.sum_lt_sum (s := Finset.univ)
    (f := fun b => nativeBadLocalWeight T b * s994VR (l := l) T In b)
    (g := fun _ => (0 : Real))
    (fun b _ =>
      mul_nonpos_of_nonneg_of_nonpos
        (nativeBadLocalWeight_nonneg T b) (le_of_lt (hVR b)))
    ⟨b0, Finset.mem_univ b0,
      mul_neg_of_pos_of_neg (nativeBadLocalWeight_pos T b0) (hVR b0)⟩
  simpa using hsum
/-- Actual paper qParameter card from per-b negativity + nonempty bad places. -/
theorem s1059PaperGlobalSign_actual
    (hVR : S1059PerBVRNegative (l := l) T In)
    (hne : S1059NonemptyBad (l := l) T) :
    Nonempty (S1051PaperQParameterCard T In) :=
  s1052PaperQParameterCard_actual T In
    (s1059PaperGlobal_neg T In hVR hne)
end LeanFormal.IUT.XiFPaper.S1059PaperGlobalSignActual
