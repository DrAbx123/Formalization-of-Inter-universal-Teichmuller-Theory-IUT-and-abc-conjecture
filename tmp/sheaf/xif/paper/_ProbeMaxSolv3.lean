import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Solvable

noncomputable section
open LeanFormal.IUT.InitialThetaSource
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2766MaximalSolvableTopActual

variable {k : Type*} [Field k]

example : isFiniteSolvableGaloisSubextension (⊤ : IntermediateField k k) := by
  refine ⟨?_, ?_, ?_⟩
  · infer_instance
  · infer_instance
  · infer_instance

end LeanFormal.IUT.XiFPaper.S2766MaximalSolvableTopActual
end
