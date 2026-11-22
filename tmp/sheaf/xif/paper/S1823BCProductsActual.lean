/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF / S1823

# S1823 -- base change along a field extension preserves finite products

The third missing field of S1769/S1794 is

  BCPreservesFiniteProducts K := PreservesFiniteProducts (baseChange K Kbar)

for Kbar = AlgebraicClosure K and baseChange K Kbar : FiniteEtale K -> FiniteEtale Kbar,
Mathlib's base change functor A |-> Kbar (x)_K A (Mathlib/RingTheory/Etale/Finite.lean).

This file proves it unconditionally, with no sorry, no new axiom and no added hypothesis.
The proof is given for an arbitrary field extension K -> L (the case Kbar = AlgebraicClosure K
of S1769 is the specialisation L = AlgebraicClosure K), so that the statement is also
available for the general geometric point of S1794.

The two mathematical inputs are

* the finite-product closure of FiniteEtale R (S1745): the Pi-algebra Pi j, A j of a finite
  family of finite etale R-algebras is again finite etale (S1745's finiteEtale_piFan_pt,
  used in piFanPt), and the Pi-fan is a limit fan in FiniteEtale R (piFanIsLimit, the
  subcategory form of S1745's piFan_isLimit);
* Algebra.TensorProduct.piRight, the algebra isomorphism
  L (x)_K (Pi i, A i) ~= Pi i, L (x)_K A i
  (Mathlib/RingTheory/TensorProduct/Pi.lean): it compares the base-changed Pi-fan with the
  Pi-fan of the base-changed factors (piRight_comp_eval), which makes the base-changed
  product cone a limit cone (bcOf_piFan_isLimit).

## Main results

* S1823.piFan, S1823.piFanIsLimit: the Pi-algebra is the product in FiniteEtale R.
* S1823.bcOf_piFan_isLimit: base change sends this product fan to a limit fan.
* S1823.bcOf_preservesFiniteProducts: base change along any field extension K -> L
  preserves finite products.
* S1823.BCPreservesFiniteProducts, S1823.bcPreservesFiniteProducts: the S1769 condition
  for Kbar = AlgebraicClosure K.
-/
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Shapes.Products
import tmp.sheaf.xif.paper.S1745FiniteEtaleLimitsActual

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace S1823

/-- The algebraic closure of K, the geometric point used in S1769 and S1794. -/
abbrev Kbar (K : Type) [Field K] : Type := AlgebraicClosure K

/-- Mathlib's base change functor A |-> L (x)_K A on finite etale algebras, for an arbitrary
field extension K -> L. -/
abbrev bcOf (K L : Type) [Field K] [Field L] [Algebra K L] :
    CommAlgCat.FiniteEtale.{0} K ⥤ CommAlgCat.FiniteEtale.{0} L :=
  CommAlgCat.FiniteEtale.baseChange K L

/-- The base change functor of S1769: A |-> Kbar (x)_K A, Kbar = AlgebraicClosure K. -/
abbrev bc (K : Type) [Field K] :
    CommAlgCat.FiniteEtale.{0} K ⥤ CommAlgCat.FiniteEtale.{0} (Kbar K) :=
  bcOf K (Kbar K)

/-! ### 1. The Pi-algebra is the product in CommAlgCat.FiniteEtale R -/

section PiFan

variable (R : Type) [Field R]

/-- The point of the product fan: the Pi-algebra.  It is a finite etale R-algebra by the
finite-product closure of S1745 (finiteEtale_piFan_pt). -/
noncomputable def piFanPt (J : Type) [Fintype J] (A : J → CommAlgCat.FiniteEtale.{0} R) :
    CommAlgCat.FiniteEtale.{0} R :=
  ⟨CommAlgCat.of R (∀ j, (A j : Type)),
    S1745.FiniteEtaleClosure.finiteEtale_piFan_pt J (fun j => (A j).obj)
      (fun j => (A j).property)⟩

/-- The product fan of a finite family of finite etale R-algebras, with point the Pi-algebra.
This is the fan of S1745 transported to the full subcategory of finite etale algebras. -/
noncomputable def piFan (J : Type) [Fintype J] (A : J → CommAlgCat.FiniteEtale.{0} R) :
    Fan A :=
  Fan.mk (piFanPt R J A)
    (fun j => CommAlgCat.FiniteEtale.ofHom (Pi.evalAlgHom R (fun j => (A j : Type)) j))

@[simp] lemma piFan_proj_apply (J : Type) [Fintype J]
    (A : J → CommAlgCat.FiniteEtale.{0} R) (j : J) (x : (piFan R J A).pt) :
    ((piFan R J A).proj j).hom.hom x = x j := rfl

set_option linter.unusedSimpArgs false in
/-- The Pi-fan is a limit fan: the finite-product closure of FiniteEtale R (S1745). -/
noncomputable def piFanIsLimit (J : Type) [Fintype J]
    (A : J → CommAlgCat.FiniteEtale.{0} R) : IsLimit (piFan R J A) := by
  refine Fan.IsLimit.mk (piFan R J A)
    (fun s => CommAlgCat.FiniteEtale.ofHom (AlgHom.pi fun j => (s.proj j).hom.hom)) ?_ ?_
  · intro s j
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    rfl
  · intro s m hm
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    funext j
    have h := congrArg (fun f => ((f : s.pt ⟶ A j)).hom.hom x) (hm j)
    simp only [ObjectProperty.FullSubcategory.comp_hom, CommAlgCat.hom_comp,
      CommAlgCat.FiniteEtale.ofHom, CommAlgCat.hom_ofHom, AlgHom.pi_apply,
      piFan_proj_apply] at h ⊢
    exact h

end PiFan

/-! ### 2. Base change and the Pi-fan -/

section PiBC

variable {K L : Type} [Field K] [Field L] [Algebra K L]

/-- The key computation: on L (x)_K (Pi i, A i), the j-th projection of the Pi-fan after
base change is the L-linearisation of the j-th projection, composed with
Algebra.TensorProduct.piRight. -/
lemma piRight_comp_eval {J : Type} [Fintype J] [DecidableEq J]
    (A : J → CommAlgCat.FiniteEtale.{0} K) (j : J) :
    (Algebra.TensorProduct.map (AlgHom.id L L)
        (Pi.evalAlgHom K (fun i => (A i : Type)) j) :
      L ⊗[K] (∀ i, (A i : Type)) →ₐ[L] L ⊗[K] (A j : Type)) =
      (Pi.evalAlgHom L (fun i => L ⊗[K] (A i : Type)) j).comp
        (Algebra.TensorProduct.piRight K L L (fun i => (A i : Type))).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro a f
  simp [Algebra.TensorProduct.piRight_tmul]

/-- Base change preserves the product fan of a finite family of finite etale algebras. -/
noncomputable def bcOf_piFan_isLimit {J : Type} [Fintype J] [DecidableEq J]
    (A : J → CommAlgCat.FiniteEtale.{0} K) :
    IsLimit ((bcOf K L).mapCone (piFan K J A)) := by
  classical
  have key : IsLimit (Fan.mk ((bcOf K L).obj (piFan K J A).pt)
      (fun j => (bcOf K L).map ((piFan K J A).proj j))) := by
    have e : (Fan.mk ((bcOf K L).obj (piFan K J A).pt)
        (fun j => (bcOf K L).map ((piFan K J A).proj j))) ≅
        piFan L J (fun j => (bcOf K L).obj (A j)) := by
      refine Fan.ext (CommAlgCat.FiniteEtale.isoMk
        (Algebra.TensorProduct.piRight K L L (fun i => (A i : Type)))) ?_
      intro j
      apply ObjectProperty.hom_ext
      apply CommAlgCat.hom_ext
      exact piRight_comp_eval A j
    exact IsLimit.ofIsoLimit (piFanIsLimit L J (fun j => (bcOf K L).obj (A j))) e.symm
  exact (isLimitMapConeFanMkEquiv (bcOf K L) A (fun j => (piFan K J A).proj j)).invFun key

end PiBC

/-! ### 3. Base change along a field extension preserves finite products -/

section FiniteProducts

variable {K L : Type} [Field K] [Field L] [Algebra K L]

/-- Base change along any field extension K -> L preserves finite products. -/
theorem bcOf_preservesFiniteProducts : PreservesFiniteProducts (bcOf K L) where
  preserves n := by
    haveI : ∀ (f : Fin n → CommAlgCat.FiniteEtale.{0} K),
        PreservesLimit (Discrete.functor f) (bcOf K L) :=
      fun f => preservesLimit_of_preserves_limit_cone (piFanIsLimit K (Fin n) f)
        (bcOf_piFan_isLimit f)
    exact preservesLimitsOfShape_of_discrete (bcOf K L)

end FiniteProducts

/-! ### 4. The condition of S1769 for Kbar = AlgebraicClosure K -/

section AlgClosure

variable (K : Type) [Field K]

/-- Base change along K -> Kbar preserves finite products: the ambient condition of S1769. -/
instance bc_preservesFiniteProducts : PreservesFiniteProducts (bc K) :=
  bcOf_preservesFiniteProducts (K := K) (L := Kbar K)

set_option linter.defProp false in
/-- The third missing field of S1769 / S1794, exactly as stated there. -/
def BCPreservesFiniteProducts : Prop :=
  PreservesFiniteProducts (CommAlgCat.FiniteEtale.baseChange.{0, 0, 0} K (AlgebraicClosure K))

/-- The third missing condition holds unconditionally. -/
theorem bcPreservesFiniteProducts : BCPreservesFiniteProducts K := by
  show PreservesFiniteProducts (bc K)
  exact bc_preservesFiniteProducts K

/-- The same statement for the abbreviation bc of S1769. -/
theorem bcPreservesFiniteProducts' : PreservesFiniteProducts (bc K) :=
  bc_preservesFiniteProducts K

end AlgClosure

end S1823
