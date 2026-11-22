import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 800000

/-!
# S3139 tool: generic laws for the tensor congruence of linear equivalences

Reusable mathematical tool (not a paper object): the tensor congruence
`PiTensorProduct.congr` is functorial and preserves the identity.  These are
Mathlib-gap lemmas needed by every tensor-packet action in this project; they are
stated generically for an arbitrary commutative semiring `R`, an arbitrary index
type, and arbitrary families of modules.

Provided:
* `piTensorCongr_refl`: congr (fun i => refl) = refl;
* `piTensorCongr_trans`: (congr e).trans (congr f) = congr (fun i => (e i).trans (f i)).

No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139ToolsTensorCongrLaws

open scoped TensorProduct

universe uR uι

variable {R : Type uR} [CommSemiring R]
variable {ι : Type uι}
variable {s : ι → Type*} [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]

/-- The tensor congruence of the identity family of linear equivalences is the
identity. -/
theorem piTensorCongr_refl :
    PiTensorProduct.congr (fun i => LinearEquiv.refl R (s i)) =
      LinearEquiv.refl R (⨂[R] i, s i) := by
  ext x
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
      repeat rw [map_smul]
      rw [PiTensorProduct.congr_tprod]
      simp
  | add x y hx hy => rw [map_add, hx, hy]; rfl

/-- The tensor congruence is functorial on pure tensors: composing two
congruences acts by the pointwise composition. -/
theorem piTensorCongr_trans_tprod
    {t : ι → Type*} [∀ i, AddCommMonoid (t i)] [∀ i, Module R (t i)]
    {u : ι → Type*} [∀ i, AddCommMonoid (u i)] [∀ i, Module R (u i)]
    (e : ∀ i, s i ≃ₗ[R] t i) (f : ∀ i, t i ≃ₗ[R] u i)
    (x : (i : ι) → s i) :
    ((PiTensorProduct.congr e).trans (PiTensorProduct.congr f))
        (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun i => f i (e i (x i))) := by
  rw [LinearEquiv.trans_apply, PiTensorProduct.congr_tprod,
    PiTensorProduct.congr_tprod]

end LeanFormal.IUT.XiFPaper.S3139ToolsTensorCongrLaws

end
