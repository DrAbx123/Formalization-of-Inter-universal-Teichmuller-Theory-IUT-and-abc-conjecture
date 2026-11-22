/- Q_p-linearity of completionMap via RingHom.toAlgebra (kurt).

The raw completions carry no global Algebra Q_p instance; carry the two Q_p-embeddings phi,psi as
explicit ring homomorphisms, build the Algebra structures by RingHom.toAlgebra, and use the
compatibility completionMap (phi c) = psi c.  No stub.
-/
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.NumberFieldFinitePlace

variable {k : Type*} [Field k] [NumberField k]
variable {K : Type*} [Field K] [NumberField K] [Algebra k K]
variable {p : Nat} [Fact p.Prime]

/-- Q_p-linearity of the completion extension map, with explicit Q_p-embeddings. -/
theorem completionMap_rat_smul (place : NumberField.FinitePlace K)
    (phi : ℚ_[p] →+* (comap (k := k) place).maximalIdeal.adicCompletion k)
    (psi : ℚ_[p] →+* place.maximalIdeal.adicCompletion K)
    (hcompat : ∀ c : ℚ_[p], completionMap (k := k) place (phi c) = psi c)
    (c : ℚ_[p]) (x : (comap (k := k) place).maximalIdeal.adicCompletion k) :
    letI : Algebra ℚ_[p] ((comap (k := k) place).maximalIdeal.adicCompletion k) := phi.toAlgebra
    letI : Algebra ℚ_[p] (place.maximalIdeal.adicCompletion K) := psi.toAlgebra
    completionMap (k := k) place (c • x) = c • completionMap (k := k) place x := by
  letI : Algebra ℚ_[p] ((comap (k := k) place).maximalIdeal.adicCompletion k) := phi.toAlgebra
  letI : Algebra ℚ_[p] (place.maximalIdeal.adicCompletion K) := psi.toAlgebra
  simp only [Algebra.smul_def]
  rw [map_mul, hcompat]

#print axioms completionMap_rat_smul

end LeanFormal.IUT.NumberFieldFinitePlace
end