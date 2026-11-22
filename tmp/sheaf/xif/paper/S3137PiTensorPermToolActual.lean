import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import LeanFormal.IUT.Audit.Status

/-!
# TOOL: pi-tensor factor-permutation linear equivalence (generic; stepxi convention identification)

**Reusable mathematical tool, not a paper object.**  Owner: lattice (manufactured
for stepxi task: SourceInd1ConventionIdentification — per-automorphism linear
comparison between polyIso in-place relabeling and procession reindexing).

Packages Mathlib's `PiTensorProduct.reindex` as a permutation equivalence with
its full composition/coherence API:
* `piTensorPermEquiv e`: pure-tensor factor permutation along `e : ι ≃ ι₂`;
* `piTensorSelfPermEquiv e V`: the same-family permutation `(⨂ i, V) ≃ₗ (⨂ i, V)`;
* `tprod` action: `perm (tprod f) = tprod (fun i => f (e.symm i))`;
* composition laws: trans, refl, symm, and compatibility with `PiTensorProduct.map`
  and the symm/refl laws; Mathlib's `PiTensorProduct.map_reindex` gives the
  map-coherence form directly when a consumer needs it.

Consumers: stepxi `S3139C3Ind1BridgeActual.SourceInd1ConventionIdentification`
(and any tensor-convention comparison).  Source: IUT III, pp. 604-620, Figures
I.4-I.6; Mathlib LinearAlgebra/PiTensorProduct/Basic.lean:677-760.
No sorry/axiom; only Mathlib reindex lemmas.  WRITE-ONLY.
-/

noncomputable section
open scoped TensorProduct
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PiTensorPermToolActual

variable {R : Type*} [CommSemiring R]
variable {ι₁ ι₂ ι₃ : Type*}
variable {s : ι₁ → Type*} [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]
variable {t : ι₁ → Type*} [∀ i, AddCommMonoid (t i)] [∀ i, Module R (t i)]

/-- **Generic tool: pure-tensor factor permutation** along an equivalence of
index types. -/
def piTensorPermEquiv (e : ι₁ ≃ ι₂) :
    (⨂[R] i : ι₁, s i) ≃ₗ[R] (⨂[R] i : ι₂, s (e.symm i)) :=
  PiTensorProduct.reindex R s e

/-- Pure-tensor action of the factor permutation: `tprod f` maps to `tprod` of
the permuted family. -/
@[simp] theorem piTensorPermEquiv_tprod (e : ι₁ ≃ ι₂) (f : Π i, s i) :
    piTensorPermEquiv (R := R) (s := s) e (PiTensorProduct.tprod R f) =
      PiTensorProduct.tprod R (fun i => f (e.symm i)) :=
  PiTensorProduct.reindex_tprod e f

/-- Composition law for the factor permutation. -/
theorem piTensorPermEquiv_trans (e : ι₁ ≃ ι₂) (e' : ι₂ ≃ ι₃) (f : ι₁ → Type*)
    [∀ i, AddCommMonoid (f i)] [∀ i, Module R (f i)] :
    (piTensorPermEquiv (R := R) (s := f) e).trans
        (piTensorPermEquiv (R := R) (s := fun i => f (e.symm i)) e') =
      piTensorPermEquiv (R := R) (s := f) (e.trans e') :=
  PiTensorProduct.reindex_trans e e'

variable {V : Type*} [AddCommMonoid V] [Module R V]

/-- **Generic tool: same-family factor permutation** `(⨂ i, V) ≃ₗ (⨂ i, V)`
for `e : ι ≃ ι` (constant family). -/
def piTensorSelfPermEquiv (e : ι₁ ≃ ι₁) :
    (⨂[R] _i : ι₁, V) ≃ₗ[R] (⨂[R] _i : ι₁, V) :=
  PiTensorProduct.reindex R (fun _ => V) e

@[simp] theorem piTensorSelfPermEquiv_tprod (e : ι₁ ≃ ι₁) (f : ι₁ → V) :
    piTensorSelfPermEquiv (R := R) (V := V) e (PiTensorProduct.tprod R f) =
      PiTensorProduct.tprod R (fun i => f (e.symm i)) :=
  PiTensorProduct.reindex_tprod e f

theorem piTensorSelfPermEquiv_trans (e e' : ι₁ ≃ ι₁) :
    (piTensorSelfPermEquiv (R := R) (V := V) e).trans
        (piTensorSelfPermEquiv (R := R) (V := V) e') =
      piTensorSelfPermEquiv (R := R) (V := V) (e.trans e') :=
  PiTensorProduct.reindex_trans e e'

@[simp] theorem piTensorSelfPermEquiv_refl :
    piTensorSelfPermEquiv (R := R) (V := V) (Equiv.refl ι₁) =
      LinearEquiv.refl R (⨂[R] _i : ι₁, V) :=
  PiTensorProduct.reindex_refl

theorem piTensorSelfPermEquiv_symm (e : ι₁ ≃ ι₁) :
    (piTensorSelfPermEquiv (R := R) (V := V) e).symm =
      piTensorSelfPermEquiv (R := R) (V := V) e.symm :=
  PiTensorProduct.reindex_symm e

end LeanFormal.IUT.XiFPaper.PiTensorPermToolActual

#check LeanFormal.IUT.XiFPaper.PiTensorPermToolActual.piTensorPermEquiv_tprod
#check LeanFormal.IUT.XiFPaper.PiTensorPermToolActual.piTensorSelfPermEquiv_trans
#check LeanFormal.IUT.XiFPaper.PiTensorPermToolActual.piTensorSelfPermEquiv_symm