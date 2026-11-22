import tmp.sheaf.xif.paper.S1059PaperGlobalSignActual
/-! # S1060: per-b qPilot negativity from measure < 1
s994VR b = log (measure (qPilot image)).  Positivity is S994's qPilot_pos;
negativity is exactly measure < 1.  The current tree has no measure scaling
formula for the finite linearized qPilot region, so this is the exact minimum. -/
noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
namespace LeanFormal.IUT.XiFPaper.S1060PerBQPilotNegActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.S1050PerBQPilotCoefficientAuditActual
open LeanFormal.IUT.XiFPaper.S1052PaperQParameterCardActual
open LeanFormal.IUT.XiFPaper.S1059PaperGlobalSignActual
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
/-- Exact per-b measure bound: qPilot image measure is below the Haar unit. -/
def S1060PerBMeasureLtOne : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    (s994H (l := l) T b (In.L b)).measure
      (s994QPilotImage (l := l) T b (In.L b)) < 1
theorem s1060VR_neg
    (hp : S1060PerBMeasureLtOne (l := l) T In) :
    S1059PerBVRNegative (l := l) T In := by
  intro b
  unfold s994VR
  have hpos := In.qPilot_pos b
  have hlt_enn : (s994H (l := l) T b (In.L b)).measure
      (s994QPilotImage (l := l) T b (In.L b)) < (1 : ENNReal) := by
    simpa [S1060PerBMeasureLtOne] using hp b
  have hlt : ((s994H (l := l) T b (In.L b)).measure
      (s994QPilotImage (l := l) T b (In.L b))).toReal < 1 := by
    have h1 : (1 : ENNReal) = ENNReal.ofReal 1 := by simp
    rw [h1] at hlt_enn
    exact ENNReal.toReal_lt_of_lt_ofReal hlt_enn
  exact (Real.log_neg_iff (ENNReal.toReal_pos hpos.ne' (ne_of_lt
    (lt_trans (hp b) ENNReal.one_lt_top)))).mpr hlt
theorem s1060PaperGlobalSign
    (hp : S1060PerBMeasureLtOne (l := l) T In)
    (hne : S1059NonemptyBad (l := l) T) :
    Nonempty (S1051PaperQParameterCard (l := l) T In) :=
  s1059PaperGlobalSign_actual (l := l) T In
    (s1060VR_neg (l := l) T In hp) hne
end LeanFormal.IUT.XiFPaper.S1060PerBQPilotNegActual
