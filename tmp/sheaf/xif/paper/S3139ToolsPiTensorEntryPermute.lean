import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 600000

/-!
# S3139 tool: entry-permutation automorphism of a tensor power (Mathlib gap)

Reusable mathematical tool (not a paper object).  Mathlib's
`PiTensorProduct.reindex` has codomain the reindexed family
`s (e.symm i)`, so it does not by itself produce an automorphism of the fixed
tensor power `⨂ i, s i` that permutes the tensor *entries*.  This file
manufactures that missing tool: given a family of linear equivalences
`h i : s (e.symm i) ≃ₗ s i` (for a constant family these are canonical
identity-type equivalences), the composition of `reindex` with the tensor
congruence `h` is an automorphism of `⨂ i, s i` acting on pure tensors by

  tprod x |-> tprod (fun i => h i (x (e.symm i))).

This is the general gap tool behind the C3 (Ind1) convention identification
(IUT III:604-620, Fig. I.4-I.6).

No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139ToolsPiTensorEntryPermute

open scoped TensorProduct

universe uR uι

variable {R : Type uR} [CommSemiring R]
variable {ι : Type uι}

section EntryPermute

variable {s : ι → Type*} [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]

/-- The entry-permutation automorphism of a tensor power: reindex by the
permutation `e` and then identify the reindexed family back with the original
one through `h`. -/
noncomputable def piTensorEntryPermute
    (e : ι ≃ ι) (h : ∀ i, s (e.symm i) ≃ₗ[R] s i) :
    (⨂[R] i, s i) ≃ₗ[R] (⨂[R] i, s i) :=
  (PiTensorProduct.reindex (R := R) (s := s) (e := e)).trans
    (PiTensorProduct.congr (s := fun i => s (e.symm i)) (t := s)
      (fun i => h i))

/-- On pure tensors the entry permutation acts by permuting the entries:
tprod x |-> tprod (fun i => h i (x (e.symm i))). -/
theorem piTensorEntryPermute_tprod
    (e : ι ≃ ι) (h : ∀ i, s (e.symm i) ≃ₗ[R] s i) (x : (i : ι) → s i) :
    piTensorEntryPermute (s := s) e h (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun i => h i (x (e.symm i))) := by
  rw [piTensorEntryPermute, LinearEquiv.trans_apply,
    PiTensorProduct.reindex_tprod, PiTensorProduct.congr_tprod]

end EntryPermute

end LeanFormal.IUT.XiFPaper.S3139ToolsPiTensorEntryPermute

end
