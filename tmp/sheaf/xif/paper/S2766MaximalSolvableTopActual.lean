import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Solvable

noncomputable section
open LeanFormal.IUT.InitialThetaSource
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2766MaximalSolvableTopActual

variable {k : Type*} [Field k]

/-- The top intermediate field is a finite solvable Galois subextension when the
base field and the ambient field coincide. -/
theorem top_isFiniteSolvableGaloisSubextension :
    isFiniteSolvableGaloisSubextension (⊤ : IntermediateField k k) := by
  refine ⟨?_, ?_, ?_⟩
  · infer_instance
  · infer_instance
  · haveI : Subsingleton
        ((⊤ : IntermediateField k k) ≃ₐ[k] (⊤ : IntermediateField k k)) :=
      ⟨fun f g => AlgEquiv.ext fun x => by
        have hx : x = algebraMap k (⊤ : IntermediateField k k) (x : k) := by
          apply Subtype.ext
          rfl
        rw [hx, AlgEquiv.commutes, AlgEquiv.commutes]⟩
    infer_instance

/-- The top intermediate field contains every finite solvable Galois
subextension. -/
theorem maximalSolvableContains_top
    (E : IntermediateField k k)
    (_hE : isFiniteSolvableGaloisSubextension E) :
    E ≤ (⊤ : IntermediateField k k) :=
  le_top

#check top_isFiniteSolvableGaloisSubextension
#check maximalSolvableContains_top
#print axioms top_isFiniteSolvableGaloisSubextension

end LeanFormal.IUT.XiFPaper.S2766MaximalSolvableTopActual
end
