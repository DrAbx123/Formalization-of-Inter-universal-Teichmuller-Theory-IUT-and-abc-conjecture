import Mathlib

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3076PhiXLinearActual

variable {K R0 : Type*} [Field K] [CommRing R0] [Algebra K R0]

#check Submodule.mem_span_pair
#check Submodule.mem_span_insert
#check Algebra.smul_def
#check Algebra.algebraMap_eq_smul_one

theorem S3076_phi_X_linear_of_degree
    (x : R0) (phi : R0 →ₗ[K] R0)
    (hdeg : phi x ∈ Submodule.span K ({1, x} : Set R0)) :
    ∃ a c : K, phi x = algebraMap K R0 a + c • x := by
  rcases (Submodule.mem_span_pair.mp hdeg) with ⟨a, c, h⟩
  refine ⟨a, c, ?_⟩
  rw [← h, Algebra.algebraMap_eq_smul_one]

#check S3076_phi_X_linear_of_degree
#print axioms S3076_phi_X_linear_of_degree

end LeanFormal.IUT.XiFPaper.S3076PhiXLinearActual
end
