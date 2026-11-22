/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF / S1810

# S1810 -- epimorphisms of finite etale K-algebras are surjective

This file proves the missing input

  S1747.EpiSurjective K

of tmp/sheaf/xif/paper/S1747FiniteEtaleMonoSplitActual.lean: every algebra map
φ : B →ₐ[K] A of finite etale K-algebras which is an epimorphism in the category of
finite etale K-algebras (with the explicit test-algebra quantifier used in S1747) is
surjective.

## Proof

Let φ : B →ₐ[K] A be such an epimorphism.  View A as a B-algebra via φ.  Since
B and A are finite etale over K, Mathlib gives

* Algebra.Etale B A (Algebra.Etale.of_restrictScalars),
* Module.Finite B A (Module.Finite.of_restrictScalars_finite).

Consider the tensor test algebra T := A ⊗[B] A.  It is finite etale over K:
Algebra.Etale A T is base change of Algebra.Etale B A, hence Algebra.Etale K T
by composition, and Module.Finite K T follows from Module.Finite B T and
Module.Finite K B.  The two canonical maps

  g a = a ⊗ₜ[B] 1,   h a = 1 ⊗ₜ[B] a   (a : A)

are K-algebra maps A → T and they agree on the image of φ, because for b : B

  φ b ⊗ₜ 1 = b • (1 ⊗ₜ 1) = 1 ⊗ₜ φ b.

By epimorphy of φ we get g = h, hence a ⊗ₜ 1 = 1 ⊗ₜ a for all a : A, i.e.
Algebra.IsEpi B A.  Mathlib's Algebra.isEpi_iff_surjective_algebraMap_of_finite
then shows that the structure map algebraMap B A -- which is φ -- is surjective.

This proof does not need the product decomposition
Algebra.Etale.iff_exists_algEquiv_prod; the tensor algebra A ⊗[B] A is the global
form of the test algebras A_i ⊗_{B_m} A_i used in the decomposition proof, and it
already suffices because the category of finite etale algebras is closed under this base
change.

Every step below is proved; no new axiom and no weakened statement is used.
-/
import Mathlib.Algebra.Algebra.Epi
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import tmp.sheaf.xif.paper.S1747FiniteEtaleMonoSplitActual

noncomputable section

open scoped TensorProduct

namespace S1810

variable {K : Type} [Field K]

set_option maxHeartbeats 1000000

/-- **Epimorphisms of finite etale algebras are surjective.**

This is the exact statement S1747.EpiSurjective K: the hypothesis hφ says that
φ is an epimorphism in the category of finite etale K-algebras, i.e. any two maps
out of A into a finite etale K-algebra which agree after precomposition with φ
are equal. -/
theorem epiSurjective : S1747.EpiSurjective K := by
  intro A B hAring hAalg hAfin hAet hBring hBalg hBfin hBet φ hφ
  -- view A as a B-algebra via φ
  letI : Algebra B A := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K B A := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro k
    exact (φ.commutes k).symm
  -- A is finite etale over B
  haveI : Algebra.Etale B A := Algebra.Etale.of_restrictScalars K B A
  haveI : Module.Finite B A := Module.Finite.of_restrictScalars_finite K B A
  -- the tensor test algebra A ⊗[B] A is finite etale over K
  have hEpi : Algebra.IsEpi B A := by
    rw [Algebra.isEpi_iff_forall_one_tmul_eq]
    intro a
    haveI : Algebra.Etale A (A ⊗[B] A) := inferInstance
    haveI : Algebra.Etale K (A ⊗[B] A) := Algebra.Etale.comp K A (A ⊗[B] A)
    haveI : Module.Finite A (A ⊗[B] A) := Module.Finite.base_change B A A
    haveI : Module.Finite K (A ⊗[B] A) := Module.Finite.trans A (A ⊗[B] A)
    -- the two canonical maps A → A ⊗[B] A
    let g : A →ₐ[K] A ⊗[B] A := Algebra.TensorProduct.includeLeft
    let h : A →ₐ[K] A ⊗[B] A :=
      (Algebra.TensorProduct.includeRight (R := B) (A := A) (B := A)).restrictScalars K
    have hg_apply : ∀ x : A, g x = x ⊗ₜ[B] (1 : A) := fun x => rfl
    have hh_apply : ∀ x : A, h x = (1 : A) ⊗ₜ[B] x := fun x => rfl
    -- they agree after precomposition with φ
    have hgh : g.comp φ = h.comp φ := by
      ext b
      rw [AlgHom.comp_apply, AlgHom.comp_apply, hg_apply, hh_apply]
      have hsm : (b : B) • (1 : A) = φ b := by
        rw [Algebra.smul_def, mul_one]
        rfl
      rw [← hsm]
      exact TensorProduct.smul_tmul (R := B) (R' := B) b (1 : A) (1 : A)
    -- epimorphy forces the two maps to be equal
    have hEq : g = h := hφ (A ⊗[B] A) g h hgh
    have := congrArg (fun f => f a) hEq
    rw [hg_apply, hh_apply] at this
    exact this.symm
  -- a finite epimorphism of algebras is surjective
  have hsurj : Function.Surjective (algebraMap B A) :=
    (Algebra.isEpi_iff_surjective_algebraMap_of_finite (R := B) (A := A)).mp hEpi
  exact fun a => hsurj a

end S1810

/-! ### Axiom audit -/

#print axioms S1810.epiSurjective
#check @S1810.epiSurjective
