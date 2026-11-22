import tmp.sheaf.xif.paper.S2793FieldOfModuliQiActual
open LeanFormal.IUT
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2793FieldOfModuliQiActual
local instance factIrr2 : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance quad2 : Algebra.IsQuadraticExtension ℚ GaussianField where
  finrank_eq_two' := LeanFormal.IUT.IUTII.Frobenioid.Example36.gaussianField_finrank
example : FiniteDimensional ℚ (⊤ : IntermediateField ℚ GaussianField) := inferInstance
example : IsGalois ℚ (⊤ : IntermediateField ℚ GaussianField) := by
  let e : (⊤ : IntermediateField ℚ GaussianField) ≃ₐ[ℚ] GaussianField := IntermediateField.topEquiv
  exact e.transfer_galois
example : IsSolvable ((⊤ : IntermediateField ℚ GaussianField) ≃ₐ[ℚ] (⊤ : IntermediateField ℚ GaussianField)) := by
  infer_instance
end LeanFormal.IUT.XiFPaper.S2793FieldOfModuliQiActual
