/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# S1746: fixed points and quotients of finite etale algebras

For a field `K`, a finite etale `K`-algebra `A`, and an action of a group `G` on `A`
by `K`-algebra automorphisms, the fixed-point subalgebra `A^G` is again finite etale
over `K`. This file constructs `A^G`, proves that it is finite and etale, and shows
that in the Galois category `(CommAlgCat.FiniteEtale K)^op` the object `A^G` is the
colimit of the action diagram. Consequently the `PreGaloisCategory` field
`hasQuotientsByFiniteGroups` is discharged for this category.

## Main results

* `finiteSplit_of_injective_pi`: a `K`-algebra embedded in a finite product of
  copies of `K` is finite split. The proof is the Chinese remainder theorem
  applied to the kernels of the coordinate projections.
* `etale_subalgebra`: every `K`-subalgebra of a finite etale `K`-algebra is
  finite etale. The proof descends along `K -> AlgebraicClosure K`, over which
  the ambient finite etale algebra becomes finite split.
* `fixedSubalgebra`, `fixedSubalgebra_etale`, `fixedSubalgebra_finite`: the fixed
  points of a group action on a finite etale algebra.
* `fixedEtale`: `A^G` packaged as an object of `CommAlgCat.FiniteEtale K`.
* `quotientCocone`, `isColimitQuotientCocone`: `A^G` is the colimit in
  `(CommAlgCat.FiniteEtale K)^op`.
* `fixedLift`, `fixedLift_fac`, `fixedLift_unique`: the algebra-level universal
  property: any compatible map `D -> A` factors uniquely through `A^G`.
* `hasQuotientsByFiniteGroups_finiteEtaleAlg`: the exact instance required by
  `PreGaloisCategory.hasQuotientsByFiniteGroups` for the category
  `FiniteEtaleAlg K = (CommAlgCat.FiniteEtale K)^op`.

## Relation to S1739

S1739 left `hasQuotientsByFiniteGroups` unproved, noting that Mathlib has no
invariant-subalgebra API for finite etale algebras. This file supplies that API
and proves the required instance. The other missing fields of S1739 (pullbacks,
finite coproducts and (G3)) are independent and remain outside this file.

To replace the field in S1739's `instPreGaloisCategory`, import this file and set

```lean
hasQuotientsByFiniteGroups := fun G _ _ =>
  S1746FiniteEtaleQuotientsActual.hasQuotientsByFiniteGroups_finiteEtaleAlg (K := K) G
```

The types agree definitionally: both `FiniteEtaleAlg` abbreviations unfold to
`(CommAlgCat.FiniteEtale.{0} K)^op`.

No placeholder proofs, extra axioms or fabricated data are used. The axiom audit
at the end reports the transitive axioms of the main declarations.
-/

import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Etale.Descent
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Basic

noncomputable section
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits

namespace S1746FiniteEtaleQuotientsActual
universe u v w

/-- The opposite of the category of finite etale `K`-algebras; this is the category
`FiniteEtaleAlg K` of S1739. -/
abbrev FiniteEtaleAlg (K : Type) [Field K] : Type 1 :=
  (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ

-- finite split lemma
theorem finiteSplit_of_injective_pi {K : Type u} [Field K] {R : Type v} [CommRing R] [Algebra K R]
    {ι : Type w} [Finite ι] (f : R →ₐ[K] (ι → K)) (hf : Function.Injective f) :
    Algebra.IsFiniteSplit K R := by
  classical
  by_cases hR : Subsingleton R
  · exact Algebra.IsFiniteSplit.of_subsingleton_top
  haveI : Nontrivial R := not_subsingleton_iff_nontrivial.mp hR
  have hι : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    haveI : IsEmpty ι := h
    exact hR (hf.subsingleton)
  let p (i : ι) : R →ₐ[K] K := (Pi.evalAlgHom K (fun _ : ι => K) i).comp f
  have hp_surj (i : ι) : Function.Surjective (p i) := by
    intro x
    refine ⟨algebraMap K R x, ?_⟩
    simp [p]
  have hp_max (i : ι) : (RingHom.ker (p i)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective (p i) (hp_surj i)
  let σ : Type v := ↥(Set.range fun i : ι => RingHom.ker (p i))
  haveI : Fintype σ := Fintype.ofFinite σ
  let rep (I : σ) : ι := Classical.choose I.property
  have rep_spec (I : σ) : RingHom.ker (p (rep I)) = (I : Ideal R) :=
    Classical.choose_spec I.property
  have hmax (I : σ) : (I : Ideal R).IsMaximal := by
    rw [← rep_spec I]
    exact hp_max (rep I)
  have hcoprime : Pairwise (Function.onFun IsCoprime (fun I : σ => (I : Ideal R))) := by
    intro I J hIJ
    haveI := hmax I
    haveI := hmax J
    exact Ideal.isCoprime_of_isMaximal (by intro h; exact hIJ (Subtype.ext h))
  have hinf : (⨅ I : σ, (I : Ideal R)) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Submodule.mem_bot]
    apply hf
    ext i
    have hx' : x ∈ (⨅ I : σ, (I : Ideal R)) := hx
    have hxker : x ∈ RingHom.ker (p i) :=
      (Submodule.mem_iInf _).mp hx' ⟨RingHom.ker (p i), ⟨i, rfl⟩⟩
    simpa [p] using hxker
  let fI : σ → Ideal R := fun I => (I : Ideal R)
  let Iinf : Ideal R := ⨅ I : σ, fI I
  let e_crt_ring : R ⧸ Iinf ≃+* ((I : σ) → R ⧸ fI I) :=
    Ideal.quotientInfRingEquivPiQuotient fI hcoprime
  let e_crt := AlgEquiv.ofRingEquiv (R := K) (f := e_crt_ring) (by
    intro x
    ext I
    trans Ideal.Quotient.mk (fI I) (algebraMap K R x)
    · rw [← Ideal.Quotient.mk_algebraMap]
      exact congrFun (Ideal.quotientInfToPiQuotient_mk fI (algebraMap K R x)) I
    · rfl)
  let qe (I : σ) := (Ideal.quotientEquivAlgOfEq K (rep_spec I).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := p (rep I)) (hp_surj (rep I)))
  let e3 := AlgEquiv.piCongrRight (fun I : σ => qe I)
  let e1 := (AlgEquiv.quotientBot K R).symm.trans (Ideal.quotientEquivAlgOfEq K hinf).symm
  let e := e1.trans (e_crt.trans e3)
  exact ⟨Fintype.card σ, ⟨e.trans (AlgEquiv.piCongrLeft' K (fun _ : σ => K) (Fintype.equivFin σ))⟩⟩

-- etale subalgebra
theorem etale_subalgebra {K : Type u} [Field K] {A : Type v} [CommRing A] [Algebra K A]
    [Module.Finite K A] [Algebra.Etale K A] (B : Subalgebra K A) :
    Algebra.Etale K B := by
  classical
  let Kbar := AlgebraicClosure K
  haveI : IsSepClosed Kbar := inferInstance
  haveI : Module.FaithfullyFlat K Kbar := inferInstance
  let i : Kbar ⊗[K] B →ₐ[Kbar] Kbar ⊗[K] A := Algebra.TensorProduct.lTensor Kbar B.val
  have hi : Function.Injective i := by
    intro x y h
    have hlin : Function.Injective (LinearMap.lTensor Kbar B.val.toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := Kbar) B.val.toLinearMap Subtype.val_injective
    exact hlin h
  haveI : Algebra.IsFiniteSplit Kbar (Kbar ⊗[K] A) := inferInstance
  obtain ⟨n, ⟨eA⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun Kbar (Kbar ⊗[K] A)
  let f : Kbar ⊗[K] B →ₐ[Kbar] (Fin n → Kbar) := eA.toAlgHom.comp i
  have hf : Function.Injective f := eA.injective.comp hi
  haveI : Algebra.IsFiniteSplit Kbar (Kbar ⊗[K] B) :=
    finiteSplit_of_injective_pi (K := Kbar) (R := Kbar ⊗[K] B) (ι := Fin n) f hf
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat (R := K) (S := B) Kbar

-- fixed subalgebra for an action
variable {K : Type} [Field K]
def fixedSubalgebra {G : Type} [Group G] {X : CommAlgCat.FiniteEtale.{0} K}
    (φ : G → (X →ₐ[K] X)) : Subalgebra K X where
  carrier := {a | ∀ g, φ g a = a}
  add_mem' := by intro a b ha hb g; simp [ha g, hb g]
  zero_mem' := by intro g; simp
  mul_mem' := by intro a b ha hb g; simp [ha g, hb g]
  one_mem' := by intro g; simp
  algebraMap_mem' := by intro k g; exact (φ g).commutes k

theorem fixedSubalgebra_etale {G : Type} [Group G] {X : CommAlgCat.FiniteEtale.{0} K}
    (φ : G → (X →ₐ[K] X)) : Algebra.Etale K (fixedSubalgebra φ) := by
  haveI : Module.Finite K X := inferInstance
  haveI : Algebra.Etale K X := inferInstance
  exact etale_subalgebra (A := X) (fixedSubalgebra φ)

theorem fixedSubalgebra_finite {G : Type} [Group G] {X : CommAlgCat.FiniteEtale.{0} K}
    (φ : G → (X →ₐ[K] X)) : Module.Finite K (fixedSubalgebra φ) := by
  haveI : Module.Finite K X := inferInstance
  exact inferInstance

/-- The fixed-point subalgebra of a finite group action on a finite etale algebra. -/
def fixedSubalgebraOfFunctor {G : Type} [Group G]
    (F : SingleObj G ⥤ (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) :
    Subalgebra K ((F.obj (SingleObj.star G)).unop) :=
  fixedSubalgebra (K := K) (G := G) (X := (F.obj (SingleObj.star G)).unop)
    (fun g : G => (F.map (SingleObj.toEnd G g)).unop.hom.hom)

theorem fixedSubalgebraOfFunctor_finite {G : Type} [Group G]
    (F : SingleObj G ⥤ (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) :
    Module.Finite K (fixedSubalgebraOfFunctor F) :=
  fixedSubalgebra_finite (φ := fun g : G => (F.map (SingleObj.toEnd G g)).unop.hom.hom)

theorem fixedSubalgebraOfFunctor_etale {G : Type} [Group G]
    (F : SingleObj G ⥤ (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) :
    Algebra.Etale K (fixedSubalgebraOfFunctor F) :=
  fixedSubalgebra_etale (φ := fun g : G => (F.map (SingleObj.toEnd G g)).unop.hom.hom)

/-- The quotient finite etale algebra `A^G`. -/
noncomputable def fixedEtale {G : Type} [Group G]
    (F : SingleObj G ⥤ (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) :
    CommAlgCat.FiniteEtale.{0} K :=
  letI : Module.Finite K (fixedSubalgebraOfFunctor F) := fixedSubalgebraOfFunctor_finite F
  letI : Algebra.Etale K (fixedSubalgebraOfFunctor F) := fixedSubalgebraOfFunctor_etale F
  CommAlgCat.FiniteEtale.of K (fixedSubalgebraOfFunctor F)

/-- The colimit cocone in `(FiniteEtale K)^op` whose point is the fixed-point algebra. -/
noncomputable def quotientCocone {G : Type} [Group G]
    (F : SingleObj G ⥤ (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) : Cocone F :=
  letI : Module.Finite K (fixedSubalgebraOfFunctor F) := fixedSubalgebraOfFunctor_finite F
  letI : Algebra.Etale K (fixedSubalgebraOfFunctor F) := fixedSubalgebraOfFunctor_etale F
  let c : F.obj (SingleObj.star G) ⟶ Opposite.op (fixedEtale F) :=
    (ObjectProperty.homMk (CommAlgCat.ofHom (fixedSubalgebraOfFunctor F).val)).op
  { pt := Opposite.op (fixedEtale F)
    ι :=
      { app := fun _ => c
        naturality := by
          intro j j' f
          rw [Subsingleton.elim j (SingleObj.star G), Subsingleton.elim j' (SingleObj.star G)]
          simp only [Functor.const_obj_map]
          apply Quiver.Hom.unop_inj
          rw [CategoryTheory.unop_comp]
          ext a
          exact a.2 f } }

noncomputable def quotientMap {G : Type} [Group G]
    (F : SingleObj G ⥤ (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) (s : Cocone F) :
    s.pt.unop.obj →ₐ[K] (F.obj (SingleObj.star G)).unop.obj :=
  (s.ι.app (SingleObj.star G)).unop.hom.hom

noncomputable def fixedLift {G : Type} [Group G]
    (F : SingleObj G ⥤ (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) (s : Cocone F) :
    s.pt.unop.obj →ₐ[K] fixedSubalgebraOfFunctor F where
  toFun x := ⟨quotientMap F s x, by
    intro g
    have h := s.ι.naturality (SingleObj.toEnd G g)
    have hraw := congrArg Quiver.Hom.unop h
    exact congrArg (fun φ => φ.hom.hom x) hraw⟩
  map_zero' := by ext; simp [quotientMap]
  map_one' := by ext; simp [quotientMap]
  map_add' := by intro x y; ext; simp [quotientMap, map_add]
  map_mul' := by intro x y; ext; simp [quotientMap, map_mul]
  commutes' := by intro k; ext; exact (s.ι.app (SingleObj.star G)).unop.hom.hom.commutes k

noncomputable def liftCocone {G : Type} [Group G]
    (F : SingleObj G ⥤ (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) (s : Cocone F) :
    s.pt.unop ⟶ fixedEtale F :=
  letI : Module.Finite K (fixedSubalgebraOfFunctor F) := fixedSubalgebraOfFunctor_finite F
  letI : Algebra.Etale K (fixedSubalgebraOfFunctor F) := fixedSubalgebraOfFunctor_etale F
  ObjectProperty.homMk (CommAlgCat.ofHom (fixedLift F s))

noncomputable def isColimitQuotientCocone {G : Type} [Group G]
    (F : SingleObj G ⥤ (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) :
    IsColimit (quotientCocone F) where
  desc s := (liftCocone F s).op
  fac s j := by
    rw [Subsingleton.elim j (SingleObj.star G)]
    apply Quiver.Hom.unop_inj
    simp only [CategoryTheory.unop_comp]
    rfl
  uniq s m hm := by
    apply Quiver.Hom.unop_inj
    have h := hm (SingleObj.star G)
    have h' := congrArg Quiver.Hom.unop h
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    ext x
    apply Subtype.ext
    have hx := congrArg (fun φ => φ.hom.hom x) h'
    exact hx

instance hasColimitsOfShape_finiteEtaleAlg (G : Type) [Group G] :
    HasColimitsOfShape (SingleObj G) (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ where
  has_colimit F :=
    HasColimit.mk (ColimitCocone.mk (quotientCocone F) (isColimitQuotientCocone F))

/-- The exact field required by `PreGaloisCategory.hasQuotientsByFiniteGroups` for the
category of finite etale `K`-algebras (opposite). -/
theorem hasQuotientsByFiniteGroups_finiteEtaleAlg (G : Type) [Group G] [Finite G] :
    HasColimitsOfShape (SingleObj G) (FiniteEtaleAlg K) :=
  hasColimitsOfShape_finiteEtaleAlg (K := K) G

theorem fixedLift_fac {G : Type} [Group G]
    (F : SingleObj G ⥤ (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) (s : Cocone F) :
    (fixedSubalgebraOfFunctor F).val.comp (fixedLift F s) = quotientMap F s := by
  ext x
  rfl

theorem fixedLift_unique {G : Type} [Group G]
    (F : SingleObj G ⥤ (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) (s : Cocone F)
    (g : s.pt.unop.obj →ₐ[K] fixedSubalgebraOfFunctor F)
    (hg : (fixedSubalgebraOfFunctor F).val.comp g = quotientMap F s) :
    g = fixedLift F s := by
  ext x
  have hx := congrArg (fun φ => φ x) hg
  simpa [fixedLift] using hx

theorem fixedEtale_finite {G : Type} [Group G]
    (F : SingleObj G ⥤ (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) :
    Module.Finite K (fixedEtale F) := inferInstance

theorem fixedEtale_etale {G : Type} [Group G]
    (F : SingleObj G ⥤ (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) :
    Algebra.Etale K (fixedEtale F) := inferInstance

theorem quotientCocone_map_unop {G : Type} [Group G]
    (F : SingleObj G ⥤ (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) :
    ((quotientCocone F).ι.app (SingleObj.star G)).unop =
      (ObjectProperty.homMk (CommAlgCat.ofHom (fixedSubalgebraOfFunctor F).val) :
        fixedEtale F ⟶ (F.obj (SingleObj.star G)).unop) := rfl




/-! ## Axiom audit -/

#print axioms finiteSplit_of_injective_pi
#print axioms etale_subalgebra
#print axioms fixedSubalgebra
#print axioms fixedSubalgebra_etale
#print axioms fixedSubalgebra_finite
#print axioms fixedSubalgebraOfFunctor_etale
#print axioms fixedSubalgebraOfFunctor_finite
#print axioms fixedEtale_finite
#print axioms fixedEtale_etale
#print axioms quotientCocone_map_unop
#print axioms isColimitQuotientCocone
#print axioms fixedLift_fac
#print axioms fixedLift_unique
#print axioms hasColimitsOfShape_finiteEtaleAlg
#print axioms hasQuotientsByFiniteGroups_finiteEtaleAlg

end S1746FiniteEtaleQuotientsActual
