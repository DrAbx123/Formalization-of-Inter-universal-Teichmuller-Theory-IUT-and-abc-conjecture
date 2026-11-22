import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Continuity of finite-dimensional normed algebra embeddings

This module proves continuity for an algebra homomorphism from a finite-dimensional
normed field over a complete nontrivially normed base field. Both field extensions
already carry compatible normed algebra structures; no norm is constructed here.
The target field need not be complete or finite-dimensional over the base field.
-/

namespace IUT.TateFiniteEmbeddingContinuity

universe baseUniverse domainUniverse codomainUniverse

variable {K : Type baseUniverse} {E : Type domainUniverse} {F : Type codomainUniverse}
  [NontriviallyNormedField K] [CompleteSpace K]
  [NormedField E] [NormedField F]
  [NormedAlgebra K E] [NormedAlgebra K F] [FiniteDimensional K E]

/-- Every algebra homomorphism with finite-dimensional domain over a complete
nontrivially normed base field is continuous for the given compatible norms. -/
theorem continuous_of_finiteDimensional (embedding : E →ₐ[K] F) : Continuous embedding :=
  embedding.toLinearMap.continuous_of_finiteDimensional

end IUT.TateFiniteEmbeddingContinuity
