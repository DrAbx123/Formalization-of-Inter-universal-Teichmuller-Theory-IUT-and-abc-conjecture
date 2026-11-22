import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport

noncomputable section
open scoped BigOperators TensorProduct Topology Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1414Probe3

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

end CompletionDegree

end LeanFormal.IUT.XiFPaper.S1414Probe3
