import LeanFormal.IUT.IUTII.Frobenioid.Example36SpecCoverEquivalence

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Foundation F1e-completion: the Spec-cover functor

Route: build the Over-level functor on plain `CommAlgCat K` under
`backward.isDefEq.respectTransparency false`, restrict to finite etale
algebras via `ObjectProperty.ι`, and lift to `FiniteEtaleCover` via
`ObjectProperty.lift`.  Boundary: field-level Spec/Gamma only; no curve Pi_1,
no theta/q-pilot claim.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SpecEssentialSurjectivity
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SpecCoverEquivalence

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36.SpecCoverFunctor

universe u

variable (K : Type u) [Field K]

section OverHelpers

variable {S : Scheme.{u}}

@[simp] lemma overMk_left {X : Scheme.{u}} (f : X ⟶ S) : (Over.mk f).left = X := rfl

@[simp] lemma overMk_hom {X : Scheme.{u}} (f : X ⟶ S) : (Over.mk f).hom = f := rfl

@[simp] lemma overHomMk_left {U V : Over S} (f : U.left ⟶ V.left) (w) :
    (Over.homMk f w : U ⟶ V).left = f := rfl

@[simp] lemma overId_left {U : Over S} : Over.Hom.left (𝟙 U) = 𝟙 U.left := rfl

@[simp] lemma overComp_left {U V W : Over S} (p : U ⟶ V) (q : V ⟶ W) :
    (p ≫ q).left = p.left ≫ q.left := rfl

end OverHelpers

def commAlgCatStructureMap (A : CommAlgCat.{u} K) : Spec (CommRingCat.of A) ⟶ specBase K :=
  Spec.map (CommRingCat.ofHom (algebraMap K A))

set_option backward.isDefEq.respectTransparency false in
noncomputable def specCoverFunctorCommAlgCat :
    (CommAlgCat.{u} K)ᵒᵖ ⥤ Over (specBase K) where
  obj A := Over.mk (commAlgCatStructureMap K A.unop)
  map {A B} f :=
    Over.homMk (Spec.map (CommRingCat.ofHom (f.unop.hom.toRingHom))) (by
      change Spec.map (CommRingCat.ofHom (f.unop.hom.toRingHom)) ≫
          (Over.mk (commAlgCatStructureMap K B.unop)).hom =
        (Over.mk (commAlgCatStructureMap K A.unop)).hom
      rw [overMk_hom, overMk_hom, commAlgCatStructureMap, commAlgCatStructureMap]
      erw [← Spec.map_comp]
      apply Spec.map_inj.mpr
      ext x
      exact f.unop.hom.commutes x)
  map_id A := by
    apply Over.OverMorphism.ext
    rw [overHomMk_left, overId_left]
    change Spec.map (CommRingCat.ofHom (CommAlgCat.Hom.hom (𝟙 A).unop).toRingHom) =
      𝟙 (Spec (CommRingCat.of (A.unop : CommAlgCat.{u} K)))
    simp [Spec.map_id]
  map_comp f g := by
    apply Over.OverMorphism.ext
    rw [overHomMk_left, overComp_left, overHomMk_left, overHomMk_left]
    rw [show (f ≫ g).unop = g.unop ≫ f.unop from rfl]
    simp only [CommAlgCat.hom_comp]
    rw [← Spec.map_comp]
    apply Spec.map_inj.mpr
    ext x
    rfl

/-- Inclusion of finite etale `K`-algebras into all `K`-algebras. -/
def finiteEtaleInclusion :
    (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ⥤ (CommAlgCat.{u} K)ᵒᵖ :=
  (ObjectProperty.ι (CommAlgCat.finiteEtale K)).op

/-- Over-level functor restricted to finite etale algebras. -/
noncomputable def specCoverFunctorOver :
    (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ⥤ Over (specBase K) :=
  finiteEtaleInclusion K ⋙ specCoverFunctorCommAlgCat K

/-- The actual functor to finite etale covers of `Spec K`. -/
noncomputable def specCoverFunctor :
    (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ⥤ FiniteEtaleCover (specBase K) :=
  ObjectProperty.lift (fun X : Over (specBase K) => IsFiniteEtaleHom X.hom)
    (specCoverFunctorOver K) (fun A => ⟨finiteEtaleAlgebraStructureMap_etale K A.unop,
      finiteEtaleAlgebraStructureMap_finite K A.unop⟩)

@[simp]
theorem specCoverFunctor_obj (A : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ) :
    (specCoverFunctor K).obj A = finiteEtaleAlgebraCover K A.unop := rfl

/-- Essential surjectivity, from F1b/F1e. -/
theorem specCoverFunctor_essentially_surjective :
    (specCoverFunctor K).EssSurj := by
  exact ⟨fun C => by
    obtain ⟨A, ⟨e⟩⟩ := finiteEtaleAlgebraCover_essentially_surjective C
    exact ⟨Opposite.op A, ⟨e.symm⟩⟩⟩

/-- **Frozen exact card.**  Full faithfulness of the actual functor and the
resulting category equivalence, with agreement with the object map.  No
inhabitant is provided. -/
structure SpecCoverFullEquivalenceCard (K : Type u) [Field K] where
  /-- Full faithfulness of the actual functor. -/
  full_faithful : (specCoverFunctor K).Full ∧ (specCoverFunctor K).Faithful
  /-- The induced equivalence. -/
  equivalence : (CommAlgCat.FiniteEtale K)ᵒᵖ ≌ FiniteEtaleCover (specBase K)
  /-- The equivalence functor is the actual functor. -/
  functor_eq : equivalence.functor = specCoverFunctor K

end LeanFormal.IUT.IUTII.Frobenioid.Example36.SpecCoverFunctor