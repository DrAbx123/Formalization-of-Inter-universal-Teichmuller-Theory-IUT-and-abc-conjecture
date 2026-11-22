import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport

noncomputable section
open scoped BigOperators TensorProduct Topology Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1414Probe1Adapted

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v

section CompletionDegree

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
variable (place : NumberField.FinitePlace K)

def s1414LowerDegreeNormalizedSignedLog
    (x : (comap (k := k) place).maximalIdeal.adicCompletion k) : ℝ :=
  - Real.log ‖x‖ / (Module.finrank ℚ k : ℝ)

def s1414UpperDegreeNormalizedSignedLog
    (x : place.maximalIdeal.adicCompletion K) : ℝ :=
  - Real.log ‖x‖ / (Module.finrank ℚ K : ℝ)

theorem s1414CompletionDegreeReadoutTransport
    (x : (comap (k := k) place).maximalIdeal.adicCompletion k) (hx : x ≠ 0) :
    s1414UpperDegreeNormalizedSignedLog (k := k) (K := K) place
        (completionMap (k := k) place x) =
      ((relativeCompletionDegree (k := k) place : ℝ) /
        (Module.finrank k K : ℝ)) *
        s1414LowerDegreeNormalizedSignedLog (k := k) place x := by
  unfold s1414UpperDegreeNormalizedSignedLog s1414LowerDegreeNormalizedSignedLog
  have h := absoluteDegreeNormalizedLogNorm_completionMap (k := k) place x hx
  rw [neg_div, neg_div]
  calc
    -(Real.log ‖completionMap (k := k) place x‖ / (Module.finrank ℚ K : ℝ))
        = -(((relativeCompletionDegree (k := k) place : ℝ) /
            (Module.finrank k K : ℝ)) *
            (Real.log ‖x‖ / (Module.finrank ℚ k : ℝ))) := by rw [h]
    _ = ((relativeCompletionDegree (k := k) place : ℝ) /
          (Module.finrank k K : ℝ)) *
          (-(Real.log ‖x‖ / (Module.finrank ℚ k : ℝ))) := by ring

theorem s1414CompletionDegreeReadoutInvariant
    (x : (comap (k := k) place).maximalIdeal.adicCompletion k) (hx : x ≠ 0) :
    s1414UpperDegreeNormalizedSignedLog (k := k) (K := K) place
        (completionMap (k := k) place x) /
      ((relativeCompletionDegree (k := k) place : ℝ) /
        (Module.finrank k K : ℝ)) =
      s1414LowerDegreeNormalizedSignedLog (k := k) place x := by
  rw [s1414CompletionDegreeReadoutTransport (k := k) (K := K) place x hx]
  have hdeg : (relativeCompletionDegree (k := k) place : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (relativeCompletionDegree_pos (k := k) place).ne'
  have hfin : (Module.finrank k K : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos (R := k) (M := K)).ne'
  have hratio : ((relativeCompletionDegree (k := k) place : ℝ) /
      (Module.finrank k K : ℝ)) ≠ 0 := div_ne_zero hdeg hfin
  field_simp [hratio]

end CompletionDegree

end LeanFormal.IUT.XiFPaper.S1414Probe1Adapted
