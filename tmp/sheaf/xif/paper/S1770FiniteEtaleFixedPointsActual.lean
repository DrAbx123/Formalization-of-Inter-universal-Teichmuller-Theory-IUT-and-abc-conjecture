/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF / S1770
-/
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.TotallySplit
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Galois.Basic

/-!
# S1770: fixed points of finite etale K-algebras and (G2) for (FiniteEtale K)^op

For a field K, a finite etale K-algebra A and a finite group G acting on A
by K-algebra automorphisms, this file

1. constructs the invariant subalgebra A^G = fixedSubalgebra of A;
2. proves that A^G is finite etale over K again (Galois descent along K -> Kbar,
   reduced to the separably closed case Kbar^n, where a subalgebra of Kbar^n is
   Kbar^m);
3. proves the universal property of A^G: in the category CommAlgCat.FiniteEtale K,
   the cone with point A^G and structural maps the inclusions A^G -> A is a limit
   cone for the action diagram (so in the opposite category (FiniteEtale K)^op,
   which is the Galois category of finite etale K-schemes, A^G is the colimit,
   i.e. the categorical quotient, with quotient map A -> A^G);
4. fills the field hasQuotientsByFiniteGroups of
   PreGaloisCategory ((CommAlgCat.FiniteEtale K)^op).

Mathlib contains neither the invariant subalgebra construction for finite etale
algebras nor the Galois descent statement that a subalgebra of a finite etale algebra is
finite etale; both are supplied here (Section 1 and Section 2).

No proof in this file is left unfinished.  The only axioms are the three standard ones
(propext, Classical.choice, Quot.sound), audited at the end of the file.

## Main results

* S1770.etale_subalgebra: a K-subalgebra of a finite etale K-algebra is etale
  (hence, being a submodule of a finite module over a field, finite etale).
* S1770.invariants: the invariant subalgebra A^G.
* S1770.invariantsCone, S1770.invariantsIsLimit: the limit cone over a
  G-action with point A^G.
* S1770.hasQuotientsByFiniteGroups: HasColimitsOfShape (SingleObj G)
  in (CommAlgCat.FiniteEtale K)^op for every finite group G.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace S1770

universe u v w

/-! ## 1. Subalgebras of finite etale algebras are finite etale

The mathematical content is Galois descent along the faithfully flat extension
K -> Kbar: over a separably closed field, a subalgebra of Kbar^n is Kbar^m.
The auxiliary statement finiteSplit_of_injective_pi is that reduction. -/

section EtaleSubalgebra

variable {K : Type u} [Field K]

/-- If a K-algebra R embeds into a finite power of a separably closed field K,
then R is K-split. -/
theorem finiteSplit_of_injective_pi {R : Type v} [CommRing R] [Algebra K R]
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

/-- A K-subalgebra of a finite etale K-algebra is etale over K.

This is Galois descent for etaleness: base change to an algebraic closure and use
that a subalgebra of a finite power of a separably closed field is split. -/
theorem etale_subalgebra {A : Type v} [CommRing A] [Algebra K A]
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
      Module.Flat.lTensor_preserves_injective_linearMap (M := Kbar) B.val.toLinearMap
        Subtype.val_injective
    exact hlin h
  haveI : Algebra.IsFiniteSplit Kbar (Kbar ⊗[K] A) := inferInstance
  obtain ⟨n, ⟨eA⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun Kbar (Kbar ⊗[K] A)
  let f : Kbar ⊗[K] B →ₐ[Kbar] (Fin n → Kbar) := eA.toAlgHom.comp i
  have hf : Function.Injective f := eA.injective.comp hi
  haveI : Algebra.IsFiniteSplit Kbar (Kbar ⊗[K] B) :=
    finiteSplit_of_injective_pi (K := Kbar) (R := Kbar ⊗[K] B) (ι := Fin n) f hf
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat (R := K) (S := B) Kbar

end EtaleSubalgebra

/-! ## 2. The invariant subalgebra -/

section FixedPoints

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A]

/-- The subalgebra of A fixed by a family of K-algebra endomorphisms indexed by G.

Only the algebra-homomorphism property of the maps is used, so this makes sense for any
family; the group law is irrelevant for the definition (and for etaleness), and enters
only through the categorical limit statement in Section 3. -/
def fixedSubalgebra (G : Type u) [Group G] (φ : G → (A →ₐ[K] A)) : Subalgebra K A where
  carrier := {a | ∀ g, φ g a = a}
  add_mem' := by intro a b ha hb g; simp [ha g, hb g]
  zero_mem' := by intro g; simp
  mul_mem' := by intro a b ha hb g; simp [ha g, hb g]
  one_mem' := by intro g; simp
  algebraMap_mem' := by intro k g; exact (φ g).commutes k

/-- Universal property of the fixed point subalgebra: any K-algebra map from a
K-algebra B into A whose image is fixed by G factors uniquely through A^G. -/
theorem existsUnique_lift_fixedSubalgebra {G : Type u} [Group G] (φ : G → (A →ₐ[K] A))
    {B : Type u} [CommRing B] [Algebra K B] (f : B →ₐ[K] A)
    (hf : ∀ (b : B) (g : G), φ g (f b) = f b) :
    ∃! F : B →ₐ[K] ↥(fixedSubalgebra G φ),
      (Subalgebra.val (fixedSubalgebra G φ)).comp F = f := by
  refine ⟨AlgHom.codRestrict f (fixedSubalgebra G φ) (fun b g => hf b g), ?_, ?_⟩
  · ext b
    rfl
  · intro F hF
    ext b
    have h := congrArg (fun (g : B →ₐ[K] A) => g b) hF
    simpa using h

end FixedPoints

/-! ## 3. A^G as the limit of the action

Let F : (SingleObj G)^op ⥤ CommAlgCat.FiniteEtale K be a G-action on a finite etale
K-algebra A (a functor out of the one-object groupoid (SingleObj G)^op whose hom
types are G^op).  We show that the cone with point A^G and structural maps the
inclusions A^G -> A is a limit cone.  Consequently (FiniteEtale K)^op has colimits of
shape SingleObj G: the quotient of A by G. -/

section Limit

variable {K : Type u} [Field K] {G : Type u} [Group G]

/-- The single object of the action shape (SingleObj G)^op. -/
def shapePoint (G : Type u) : (SingleObj G)ᵒᵖ := Opposite.op (SingleObj.star G)

/-- The finite etale K-algebra carrying the action. -/
abbrev actionAlgebra (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K) : Type u :=
  F.obj (shapePoint G)

/-- The action of g : G on A = actionAlgebra F. -/
def actionMap (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K) (g : G) :
    actionAlgebra F →ₐ[K] actionAlgebra F :=
  (F.map (Opposite.op g)).hom.hom

/-- The invariant subalgebra A^G. -/
def invariants (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K) :
    Subalgebra K (actionAlgebra F) :=
  fixedSubalgebra (K := K) (A := actionAlgebra F) G (actionMap F)

instance invariantsFinite (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K) :
    Module.Finite K ↥(invariants F) :=
  inferInstance

/-- A^G is etale over K: it is a subalgebra of the finite etale algebra A. -/
instance invariantsEtale (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K) :
    Algebra.Etale K ↥(invariants F) :=
  etale_subalgebra (invariants F)

/-- The invariant subalgebra A^G, as an object of the category of finite etale
K-algebras. -/
def invariantsObject (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K) :
    CommAlgCat.FiniteEtale.{u} K :=
  CommAlgCat.FiniteEtale.of K ↥(invariants F)

/-- The structural map A^G -> A of the cone over the action. -/
def invariantsMap (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K)
    (j : (SingleObj G)ᵒᵖ) : invariantsObject F ⟶ F.obj j :=
  { hom := CommAlgCat.ofHom
      (Subalgebra.val (invariants F) : ↥(invariants F) →ₐ[K] (F.obj j).obj) }

/-- The quotient map A -> A^G, viewed in the opposite category (FiniteEtale K)^op. -/
def quotientMap (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K) :
    Opposite.op (F.obj (shapePoint G)) ⟶ Opposite.op (invariantsObject F) :=
  Quiver.Hom.op (invariantsMap F (shapePoint G))

/-- The structural maps are compatible with the action: this is the defining property
of A^G. -/
theorem invariantsMap_naturality (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K)
    {j j' : (SingleObj G)ᵒᵖ} (f : j ⟶ j') :
    invariantsMap F j' = invariantsMap F j ≫ F.map f := by
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  show (Subalgebra.val (invariants F) : ↥(invariants F) →ₐ[K] (F.obj j').obj) =
    ((F.map f).hom.hom).comp
      (Subalgebra.val (invariants F) : ↥(invariants F) →ₐ[K] (F.obj j).obj)
  apply AlgHom.ext
  intro x
  show (Subalgebra.val (invariants F)) x =
    ((F.map f).hom.hom) ((Subalgebra.val (invariants F)) x)
  have hf : f = Opposite.op (Opposite.unop f) := (Opposite.op_unop f).symm
  rw [hf]
  exact (x.2 (Opposite.unop f)).symm

/-- The cone over a G-action with point A^G and structural maps the inclusions
A^G -> A. -/
def invariantsCone (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K) : Cone F where
  pt := invariantsObject F
  π :=
    { app := invariantsMap F
      naturality := by
        intro j j' f
        exact invariantsMap_naturality F f }

/-- The factorisation of an arbitrary cone over the action through A^G. -/
def invariantsLift (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K) (c : Cone F) :
    c.pt ⟶ (invariantsCone F).pt :=
  { hom := CommAlgCat.ofHom
      (AlgHom.codRestrict ((c.π.app (shapePoint G)).hom.hom) (invariants F) (by
        intro x
        show ∀ g : G, actionMap F g ((c.π.app (shapePoint G)).hom.hom x) =
          (c.π.app (shapePoint G)).hom.hom x
        intro g
        exact congrArg (fun (m : c.pt ⟶ F.obj (shapePoint G)) => m.hom.hom x)
          (Cone.w (j := shapePoint G) (j' := shapePoint G) c (Opposite.op g)))) }

/-- The factorisation given by invariantsLift makes the triangles commute. -/
theorem invariantsLift_fac (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K)
    (c : Cone F) (j : (SingleObj G)ᵒᵖ) :
    invariantsLift F c ≫ (invariantsCone F).π.app j = c.π.app j := by
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  rfl

/-- Universal property of A^G. The cone invariantsCone F is a limit cone: every
cone over the G-action factors uniquely through A^G = invariants F. -/
def invariantsIsLimit (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K) :
    IsLimit (invariantsCone F) where
  lift := invariantsLift F
  fac := invariantsLift_fac F
  uniq c m hm := by
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    have h3 : m ≫ (invariantsCone F).π.app (shapePoint G) =
        invariantsLift F c ≫ (invariantsCone F).π.app (shapePoint G) := by
      rw [hm (shapePoint G), invariantsLift_fac F c (shapePoint G)]
    have h4 := congrArg (fun (g : c.pt ⟶ F.obj (shapePoint G)) => (g.hom.hom) x) h3
    exact Subtype.ext h4

instance hasLimitInvariants (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K) :
    HasLimit F :=
  HasLimit.mk ⟨invariantsCone F, invariantsIsLimit F⟩

/-- CommAlgCat.FiniteEtale K has all limits of shape (SingleObj G)^op: the limit of a
G-action is its invariant subalgebra. -/
instance hasLimitsOfShapeOpSingleObj :
    HasLimitsOfShape (SingleObj G)ᵒᵖ (CommAlgCat.FiniteEtale.{u} K) :=
  ⟨fun F => hasLimitInvariants F⟩

end Limit

/-! ## 4. The quotient and (G2) for (FiniteEtale K)^op -/

section Quotients

variable {K : Type u} [Field K]

/-- The category of finite etale K-algebras, opposite to the category of finite etale
affine K-schemes.  This is the Galois category whose objects are finite etale covers of
Spec K. -/
abbrev FiniteEtaleAlg (K : Type u) [Field K] : Type (u + 1) :=
  (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ

namespace FiniteEtaleAlg

instance category : Category.{u, u + 1} (FiniteEtaleAlg K) := inferInstance

/-- Lenstra (G2), field hasQuotientsByFiniteGroups.  For every finite group G,
the category (FiniteEtale K)^op has colimits of shape SingleObj G.

The colimit of a G-action on a finite etale algebra A is its invariant subalgebra
A^G, with quotient map A -> A^G in (FiniteEtale K)^op (the opposite of the
inclusion A^G -> A). -/
instance hasQuotientsByFiniteGroups (G : Type u) [Group G] [Finite G] :
    HasColimitsOfShape (SingleObj G) (FiniteEtaleAlg K) :=
  hasColimitsOfShape_op_of_hasLimitsOfShape (J := SingleObj G)
    (C := CommAlgCat.FiniteEtale.{u} K)

end FiniteEtaleAlg

end Quotients

/-! ## 5. Filling the hasQuotientsByFiniteGroups field

PreGaloisCategory has five axioms.  This file proves the fourth one
(hasQuotientsByFiniteGroups) unconditionally; the assembly below shows that it can be
plugged into the structure, leaving the other fields as hypotheses. -/

section Assembly

variable {K : Type u} [Field K]

/-- The exact statement of the fourth field of PreGaloisCategory (FiniteEtaleAlg K). -/
abbrev HasQuotientsByFiniteGroupsField : Prop :=
  forall (G : Type u) [Group G] [Finite G],
    HasColimitsOfShape (SingleObj G) (FiniteEtaleAlg K)

/-- The field is now unconditional. -/
theorem hasQuotientsByFiniteGroupsField_holds :
    HasQuotientsByFiniteGroupsField (K := K) :=
  fun _ _ _ => inferInstance

/-- Assembling a PreGaloisCategory (FiniteEtaleAlg K) from the other four fields: the
fourth field (hasQuotientsByFiniteGroups) is supplied by the invariant subalgebra. -/
theorem preGaloisCategoryOfOtherFields
    (hTerm : HasTerminal (FiniteEtaleAlg K))
    (hPull : HasPullbacks (FiniteEtaleAlg K))
    (hCoprod : HasFiniteCoproducts (FiniteEtaleAlg K))
    (hMono : forall {X Y : FiniteEtaleAlg K} (i : X ⟶ Y), Mono i →
      ∃ (Z : FiniteEtaleAlg K) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u))) :
    PreGaloisCategory (FiniteEtaleAlg K) where
  hasTerminal := hTerm
  hasPullbacks := hPull
  hasFiniteCoproducts := hCoprod
  hasQuotientsByFiniteGroups := fun _ _ _ => inferInstance
  monoInducesIsoOnDirectSummand := hMono

end Assembly

/-! ## 6. Axiom audit -/

#print axioms S1770.finiteSplit_of_injective_pi
#print axioms S1770.etale_subalgebra
#print axioms S1770.fixedSubalgebra
#print axioms S1770.invariants
#print axioms S1770.invariantsFinite
#print axioms S1770.invariantsEtale
#print axioms S1770.invariantsCone
#print axioms S1770.invariantsLift
#print axioms S1770.existsUnique_lift_fixedSubalgebra
#print axioms S1770.quotientMap
#print axioms S1770.invariantsLift_fac
#print axioms S1770.invariantsIsLimit
#print axioms S1770.hasLimitInvariants
#print axioms S1770.hasLimitsOfShapeOpSingleObj
#print axioms S1770.FiniteEtaleAlg.hasQuotientsByFiniteGroups
#print axioms S1770.hasQuotientsByFiniteGroupsField_holds
#print axioms S1770.preGaloisCategoryOfOtherFields

end S1770