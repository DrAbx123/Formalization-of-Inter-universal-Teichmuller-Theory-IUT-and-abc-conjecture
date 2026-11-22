
import tmp.sheaf.xif.paper.S1858GlobalTraceActual
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Finite

noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
open scoped TensorProduct
open LinearMap

namespace LeanFormal.IUT.XiFPaper.S1859ProjectiveTraceActual

section Cover

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A finite free cover of `M` together with a splitting. -/
structure FreeCover where
  n : ℕ
  p : (Fin n → R) →ₗ[R] M
  i : M →ₗ[R] Fin n → R
  hpi : p ∘ₗ i = LinearMap.id

variable {F F' : Type*} [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Finite R F]
  [AddCommGroup F'] [Module R F'] [Module.Free R F'] [Module.Finite R F']

/-- The trace computed from a free cover is independent of the cover. -/
theorem trace_eq_of_covers {p : F →ₗ[R] M} {i : M →ₗ[R] F} (hpi : p ∘ₗ i = LinearMap.id)
    {p' : F' →ₗ[R] M} {i' : M →ₗ[R] F'} (hpi' : p' ∘ₗ i' = LinearMap.id)
    (f : M →ₗ[R] M) :
    LinearMap.trace R F (i ∘ₗ f ∘ₗ p) = LinearMap.trace R F' (i' ∘ₗ f ∘ₗ p') := by
  have h1 : ∀ y, p' (i' y) = y := fun y => DFunLike.congr_fun hpi' y
  have h2 : ∀ y, p (i y) = y := fun y => DFunLike.congr_fun hpi y
  let A : F' →ₗ[R] F := i ∘ₗ f ∘ₗ p'
  let B : F →ₗ[R] F' := i' ∘ₗ p
  have hAB : A ∘ₗ B = i ∘ₗ f ∘ₗ p := by
    ext x
    simp [A, B, h1]
  have hBA : B ∘ₗ A = i' ∘ₗ f ∘ₗ p' := by
    ext x
    simp [A, B, h2]
  rw [← hAB, ← hBA]
  exact LinearMap.trace_comp_comm' B A

end Cover
