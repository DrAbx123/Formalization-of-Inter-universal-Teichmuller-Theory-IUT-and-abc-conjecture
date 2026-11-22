import tmp.sheaf.xif.paper.S1051PaperGlobalFinalActual
/-! # S1052: actual S1051PaperQParameterCard from paperGlobalQPilotLog
qParameter := exp(paperGlobalQPilotLog).  Positivity/log-nonvanishing are
automatic; the absolute-value identity needs negativity of the paper global
qPilot scalar, recorded as the exact minimal sign input. -/
noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
namespace LeanFormal.IUT.XiFPaper.S1052PaperQParameterCardActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.S1050PerBQPilotCoefficientAuditActual
open LeanFormal.IUT.XiFPaper.S1051PaperGlobalFinalActual
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
/-- Exact minimal sign input for the paper global qPilot. -/
def S1052PaperGlobalNeg : Prop :=
  s1050PaperGlobalQPilotLog T In < 0
theorem s1052PaperGlobal_ne_zero
    (hneg : S1052PaperGlobalNeg T In) :
    s1050PaperGlobalQPilotLog T In ≠ 0 :=
  ne_of_lt hneg
/-- Actual paper qParameter card, conditional on the sign input. -/
noncomputable def s1052PaperQParameterCard
    (hneg : S1052PaperGlobalNeg T In) :
    S1051PaperQParameterCard T In where
  qParameter := Real.exp (s1050PaperGlobalQPilotLog T In)
  qParameter_pos := Real.exp_pos _
  qParameter_log_ne_zero := by
    rw [Real.log_exp]
    exact s1052PaperGlobal_ne_zero T In hneg
  qPilotLogVolume_eq := by
    rw [Real.log_exp]
    have h := hneg
    rw [abs_of_neg h]
    ring
theorem s1052PaperQParameterCard_actual
    (hneg : S1052PaperGlobalNeg T In) :
    Nonempty (S1051PaperQParameterCard T In) :=
  ⟨s1052PaperQParameterCard T In hneg⟩
end LeanFormal.IUT.XiFPaper.S1052PaperQParameterCardActual
