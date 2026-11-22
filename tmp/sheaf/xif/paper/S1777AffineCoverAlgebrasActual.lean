import tmp.sheaf.xif.paper.S1743CoverSliceActual
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# S1777: finite etale covers of the affine model versus finite etale algebras

The S1726 orbicurve S1726Orbicurve is the representable etale stack of the
affine scheme Spec R' with R' = S1726CoordinateRing.  The D6 finite etale
covers of that orbicurve live in Iut.OrbicurveFiniteEtaleCover S1726Orbicurve:
they are category-valued etale stacks over Spec F' mapping to the representable
stack of Spec R' with representably finite etale structure map.

The task of this file is the comparison

  OrbicurveFiniteEtaleCover S1726Orbicurve   ~=   (CommAlgCat.FiniteEtale R')^op,

and it is split into two genuinely different halves.

## 1. The affine algebra/scheme dictionary

At the level of affine models the algebra/scheme correspondence is formal.  The
functor

  S1777SliceFunctor : (CommAlgCat.FiniteEtale R')^op --> S1733Slice

sends a finite etale R'-algebra A to the ring A together with the structure
morphism Spec A --> Spec R' (S1733Slice is S1733's affine finite etale slice
over Spec R').  It is proved here to be full and faithful:

* faithfulness is injectivity of Spec.map on ring maps, plus CommAlgCat.hom_ext
  (S1777SliceFunctor_faithful);
* fullness reconstructs the R'-algebra map from a morphism Spec A --> Spec B of
  affine models by passing to global sections and using that the resulting
  triangle commutes (S1777SliceFunctor_full).

## 2. The affine algebra/scheme equivalence (proved)

The essential surjectivity of S1777SliceFunctor is proved as well, so the affine
dictionary is a genuine equivalence of categories (S1777SliceEquiv):

* the global-sections algebra map S1777AlgMap is built from Scheme.Gamma-Spec,
  X.hom.appTop and Scheme.GammaSpecIso;
* Spec.map (S1777AlgMap X) = X.hom is S1777SpecMapAlgMap, from
  Scheme.isoSpec_hom_naturality;
* global sections of a finite etale affine scheme form a finite etale algebra:
  S1777AppTop_finite, S1777AppTop_etale, S1777AlgMap_finite, S1777AlgMap_etale;
* hence S1777SliceAlgebra X is a finite etale R'-algebra and the canonical map
  S1777SliceIso X : S1777Obj (S1777SliceAlgebra X) ≅ X is an isomorphism of the
  slice (S1777Obj_sliceAlgebra_left, S1777Obj_sliceAlgebra_hom).

## 3. The exact first missing theorem

What remains genuinely geometric is the comparison with the *stacks*.  The actual
covers are category-valued etale stacks, not schemes, so the affine dictionary
alone does not identify them.  The missing theorem is (M2)
S1777StackComparison, S1733's S1733CoverSliceEquivalence, equivalently S1743's
S1743CoverSliceComparison:

* representability of finite etale covers of the affine base by affine finite
  etale schemes, for stacks rather than for schemes, and
* full faithfulness of the resulting comparison functor (cover maps modulo
  2-isomorphism correspond to scheme maps of the affine models).

Both are absent from the tree; S1743 records exactly this comparison.

## 4. What is proved about the target

The target equivalence between the actual stack-valued covers and
(CommAlgCat.FiniteEtale R')^op is *equivalent* to (M2)
(S1777TargetEquivalence_iff).  Nothing is lost or added by this reduction, so
the residual gap is exactly (M2); in particular the algebra side is provably not
the gap.  Consequently an inhabitant of S1743CoverSliceComparison yields the
target equivalence (S1777TargetEquivalence_of_comparison).

The target equivalence itself is not asserted, and no equivalence is faked: the
conditional theorem takes S1743's comparison explicitly as a hypothesis.  The
affine equivalence S1777SliceEquiv is unconditional.

## Axioms

Only propext, Classical.choice and Quot.sound are used; see the #print axioms
block at the end.  No sorry, no new axiom.
-/


noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1777AffineCoverAlgebrasActual

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual

/-! ## 1. Notation: R', the base scheme, finite etale algebras -/

/-- The coordinate ring R' of the affine model of E'. -/
abbrev S1777R : Type := S1726CoordinateRing

/-- The affine base Spec R'. -/
abbrev S1777Base : Scheme.{0} := S1733BaseScheme

/-- The category of finite etale R'-algebras. -/
abbrev S1777Alg : Type 1 := CommAlgCat.FiniteEtale.{0} S1777R

/-- The structure morphism Spec A -> Spec R' of a finite etale algebra. -/
noncomputable def S1777StructMap (A : CommAlgCat.FiniteEtale.{0} S1777R) :
    Spec (CommRingCat.of (↥A)) ⟶ S1777Base :=
  Spec.map (CommRingCat.ofHom (algebraMap S1777R (↥A)))

lemma S1777StructMap_isFinite (A : CommAlgCat.FiniteEtale.{0} S1777R) :
    IsFinite (S1777StructMap A) := by
  rw [S1777StructMap, IsFinite.SpecMap_iff, CommRingCat.hom_ofHom]
  exact RingHom.finite_algebraMap.mpr inferInstance

lemma S1777StructMap_etale (A : CommAlgCat.FiniteEtale.{0} S1777R) :
    Etale (S1777StructMap A) := by
  rw [S1777StructMap, HasRingHomProperty.Spec_iff (P := @Etale) (Q := @RingHom.Etale),
    CommRingCat.hom_ofHom]
  exact RingHom.etale_algebraMap.mpr inferInstance

/-! ## 2. The algebra/scheme functor to the affine finite etale slice -/

/-- The object map A |-> (Spec A -> Spec R'). -/
noncomputable def S1777Obj (A : S1777Algᵒᵖ) : S1733Slice :=
  MorphismProperty.CostructuredArrow.mk (Q := ⊤) (P := S1733FiniteEtale)
    (F := Scheme.Spec) (X := S1777Base) (S1777StructMap A.unop)
    ⟨S1777StructMap_isFinite A.unop, S1777StructMap_etale A.unop⟩

@[simp] lemma S1777Obj_left (A : S1777Algᵒᵖ) :
    (S1777Obj A).left = Opposite.op (CommRingCat.of (↥A.unop)) := rfl

@[simp] lemma S1777Obj_hom (A : S1777Algᵒᵖ) :
    (S1777Obj A).hom = S1777StructMap A.unop := rfl

/-- The algebra-map relation on components. -/
lemma S1777StructMap_comp {A B : S1777Algᵒᵖ} (g : A ⟶ B) :
    CommRingCat.ofHom (algebraMap S1777R (↥B.unop)) ≫
        CommRingCat.ofHom g.unop.hom.hom.toRingHom =
      CommRingCat.ofHom (algebraMap S1777R (↥A.unop)) := by
  rw [← CommRingCat.ofHom_comp]
  apply congrArg CommRingCat.ofHom
  apply RingHom.ext
  intro x
  exact g.unop.hom.hom.commutes x

/-- The triangle Spec B -> Spec A -> Spec R'. -/
lemma S1777StructMap_triangle {A B : S1777Algᵒᵖ} (g : A ⟶ B) :
    Scheme.Spec.map
        (Opposite.op (CommRingCat.ofHom g.unop.hom.hom.toRingHom)) ≫
        S1777StructMap B.unop = S1777StructMap A.unop := by
  show Spec.map (CommRingCat.ofHom g.unop.hom.hom.toRingHom) ≫
      S1777StructMap B.unop = S1777StructMap A.unop
  rw [S1777StructMap, S1777StructMap, ← Spec.map_comp]
  exact congrArg Spec.map (S1777StructMap_comp g)

/-- The algebra/scheme functor (CommAlgCat.FiniteEtale R')^op -> S1733Slice. -/
noncomputable def S1777SliceFunctor : S1777Algᵒᵖ ⥤ S1733Slice where
  obj := S1777Obj
  map {A B} g :=
    MorphismProperty.CostructuredArrow.homMk (Q := ⊤) (P := S1733FiniteEtale)
      (F := Scheme.Spec) (X := S1777Base)
      (Opposite.op (CommRingCat.ofHom g.unop.hom.hom.toRingHom)) (by trivial)
      (S1777StructMap_triangle g)
  map_id A := by
    apply MorphismProperty.CostructuredArrow.Hom.ext
    show (Opposite.op (CommRingCat.ofHom (𝟙 A).unop.hom.hom.toRingHom) : _) =
      𝟙 (Opposite.op (CommRingCat.of (↥A.unop)))
    rw [show (𝟙 A).unop.hom.hom.toRingHom = RingHom.id (↥A.unop) from rfl,
      CommRingCat.ofHom_id]
    exact CategoryTheory.op_id
  map_comp {A B C} g h := by
    apply MorphismProperty.CostructuredArrow.Hom.ext
    rfl

/-- Faithfulness: a morphism of affine finite etale models is determined by its
underlying ring map, by injectivity of Spec.map. -/
instance S1777SliceFunctor_faithful : S1777SliceFunctor.Faithful where
  map_injective {A B} f g h := by
    have hleft : (S1777SliceFunctor.map f).left = (S1777SliceFunctor.map g).left :=
      congrArg (fun φ => φ.left) h
    have h1 : (CommRingCat.ofHom f.unop.hom.hom.toRingHom) =
        (CommRingCat.ofHom g.unop.hom.hom.toRingHom) := Quiver.Hom.op_inj hleft
    have h2 : f.unop.hom.hom.toRingHom = g.unop.hom.hom.toRingHom :=
      congrArg CommRingCat.Hom.hom h1
    have h3 : f.unop.hom.hom = g.unop.hom.hom :=
      AlgHom.ext (fun x => congrArg (fun φ => φ x) h2)
    have h4 : f.unop.hom = g.unop.hom := CommAlgCat.hom_ext h3
    have h5 : f.unop = g.unop := InducedCategory.hom_ext h4
    exact Opposite.unop_injective h5

/-- The commuting triangle of a slice morphism Spec A -> Spec B. -/
lemma S1777SliceHom_algMap_comp {A B : S1777Algᵒᵖ} (φ : S1777Obj A ⟶ S1777Obj B) :
    CommRingCat.ofHom (algebraMap S1777R (↥B.unop)) ≫ φ.left.unop =
      CommRingCat.ofHom (algebraMap S1777R (↥A.unop)) := by
  have htri : Scheme.Spec.map φ.left ≫ (S1777Obj B).hom = (S1777Obj A).hom := φ.w
  have hgoal : Spec.map (CommRingCat.ofHom (algebraMap S1777R (↥B.unop)) ≫ φ.left.unop) =
      Spec.map (CommRingCat.ofHom (algebraMap S1777R (↥A.unop))) := by
    rw [Spec.map_comp]
    exact htri
  exact Spec.map_injective hgoal

/-- Fullness: every morphism of affine finite etale models is Spec.map of the
R'-algebra map on global sections. -/
instance S1777SliceFunctor_full : S1777SliceFunctor.Full where
  map_surjective {A B} φ := by
    have hcomm : CommRingCat.ofHom (algebraMap S1777R (↥B.unop)) ≫ φ.left.unop =
        CommRingCat.ofHom (algebraMap S1777R (↥A.unop)) := S1777SliceHom_algMap_comp φ
    let g' : ↥(B.unop).obj →+* ↥(A.unop).obj := CommRingCat.Hom.hom φ.left.unop
    have hcomp : g'.comp (algebraMap S1777R (↥(B.unop).obj)) =
        algebraMap S1777R (↥(A.unop).obj) := by
      have h := congrArg CommRingCat.Hom.hom hcomm
      simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp] at h
      exact h
    let ψ : ↥(B.unop).obj →ₐ[S1777R] ↥(A.unop).obj :=
      { toRingHom := g'
        commutes' := fun x => by
          have h := congrFun (congrArg DFunLike.coe hcomp) x
          simpa [RingHom.comp_apply] using h }
    let ghom : B.unop ⟶ A.unop := InducedCategory.homMk (CommAlgCat.ofHom ψ)
    refine ⟨ghom.op, ?_⟩
    apply MorphismProperty.CostructuredArrow.Hom.ext
    show (Opposite.op (CommRingCat.ofHom (CommRingCat.Hom.hom φ.left.unop)) : _) = φ.left
    rw [CommRingCat.ofHom_hom]
    exact Quiver.Hom.op_unop φ.left


/-! ## 3. The global-sections algebra of an affine finite etale model -/

/-- The R'-algebra map on global sections of an affine finite etale model
X -> Spec R', read through Spec and global sections. -/
noncomputable def S1777AlgMap (X : S1733Slice) :
    CommRingCat.of S1777R ⟶ X.left.unop :=
  (Scheme.ΓSpecIso (CommRingCat.of S1777R)).inv ≫ X.hom.appTop ≫
    (Scheme.ΓSpecIso X.left.unop).hom

/-- The spectrum of the global-sections algebra map is the original structure
morphism: this is Scheme.isoSpec_hom_naturality for the affine model. -/
theorem S1777SpecMapAlgMap (X : S1733Slice) :
    Spec.map (S1777AlgMap X) = X.hom := by
  haveI hbase : IsAffine S1733BaseScheme := inferInstance
  haveI : IsAffine ((Functor.fromPUnit S1733BaseScheme).obj X.right) := hbase
  have h0 := Scheme.isoSpec_hom_naturality X.hom
  have h : (Spec X.left.unop).isoSpec.hom ≫ Spec.map X.hom.appTop =
      X.hom ≫ (Spec (CommRingCat.of S1777R)).isoSpec.hom := h0
  rw [Scheme.isoSpec_Spec_hom, Scheme.isoSpec_Spec_hom] at h
  rw [← Spec.map_comp] at h
  have hominv : Spec.map (Scheme.ΓSpecIso (CommRingCat.of S1777R)).hom ≫
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of S1777R)).inv =
        𝟙 (Spec (CommRingCat.of S1777R)) := by
    rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  calc Spec.map (S1777AlgMap X)
      = Spec.map (X.hom.appTop ≫ (Scheme.ΓSpecIso X.left.unop).hom) ≫
          Spec.map (Scheme.ΓSpecIso (CommRingCat.of S1777R)).inv := by
        rw [S1777AlgMap, Spec.map_comp]
    _ = (X.hom ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of S1777R)).hom) ≫
          Spec.map (Scheme.ΓSpecIso (CommRingCat.of S1777R)).inv := by rw [h]
    _ = X.hom := by
        rw [Category.assoc, hominv]
        exact Category.comp_id X.hom

lemma S1777AppTop_finite (X : S1733Slice) :
    RingHom.Finite (X.hom.appTop).hom := by
  haveI hbase : IsAffine S1733BaseScheme := inferInstance
  haveI : IsAffine ((Functor.fromPUnit S1733BaseScheme).obj X.right) := hbase
  exact (X.prop.1).finite_app ⊤ (isAffineOpen_top _)

lemma S1777AppTop_etale (X : S1733Slice) :
    RingHom.Etale (X.hom.appTop).hom := by
  haveI hbase : IsAffine S1733BaseScheme := inferInstance
  haveI : IsAffine ((Functor.fromPUnit S1733BaseScheme).obj X.right) := hbase
  exact (X.prop.2).etale_appLE (U := ⊤) (isAffineOpen_top _) (V := ⊤)
    (isAffineOpen_top _) le_top

lemma S1777FiniteOfIso {A B : CommRingCat} (f : A ⟶ B) [IsIso f] :
    RingHom.Finite f.hom :=
  RingHom.Finite.of_surjective f.hom
    ((ConcreteCategory.isIso_iff_bijective f).mp inferInstance).2

lemma S1777EtaleOfIso {A B : CommRingCat} (f : A ⟶ B) [IsIso f] :
    RingHom.Etale f.hom :=
  RingHom.Etale.of_bijective ((ConcreteCategory.isIso_iff_bijective f).mp inferInstance)

/-- Global sections of a finite etale affine model form a module-finite
R'-module. -/
lemma S1777AlgMap_finite (X : S1733Slice) : RingHom.Finite (S1777AlgMap X).hom := by
  have h1 : RingHom.Finite (X.hom.appTop).hom := S1777AppTop_finite X
  have h2 : RingHom.Finite
      ((Scheme.ΓSpecIso X.left.unop).hom.hom.comp (X.hom.appTop).hom) :=
    RingHom.Finite.comp (S1777FiniteOfIso (Scheme.ΓSpecIso X.left.unop).hom) h1
  have h3 : RingHom.Finite
      (((Scheme.ΓSpecIso X.left.unop).hom.hom.comp (X.hom.appTop).hom).comp
        (Scheme.ΓSpecIso (CommRingCat.of S1777R)).inv.hom) :=
    RingHom.Finite.comp h2
      (S1777FiniteOfIso (Scheme.ΓSpecIso (CommRingCat.of S1777R)).inv)
  rw [S1777AlgMap, CommRingCat.hom_comp, CommRingCat.hom_comp]
  exact h3

/-- Global sections of a finite etale affine model form an etale R'-algebra. -/
lemma S1777AlgMap_etale (X : S1733Slice) : RingHom.Etale (S1777AlgMap X).hom := by
  have h1 : RingHom.Etale (X.hom.appTop).hom := S1777AppTop_etale X
  have h2 : RingHom.Etale
      ((Scheme.ΓSpecIso X.left.unop).hom.hom.comp (X.hom.appTop).hom) :=
    RingHom.Etale.stableUnderComposition _ _ h1
      (S1777EtaleOfIso (Scheme.ΓSpecIso X.left.unop).hom)
  have h3 : RingHom.Etale
      (((Scheme.ΓSpecIso X.left.unop).hom.hom.comp (X.hom.appTop).hom).comp
        (Scheme.ΓSpecIso (CommRingCat.of S1777R)).inv.hom) :=
    RingHom.Etale.stableUnderComposition _ _
      (S1777EtaleOfIso (Scheme.ΓSpecIso (CommRingCat.of S1777R)).inv) h2
  rw [S1777AlgMap, CommRingCat.hom_comp, CommRingCat.hom_comp]
  exact h3


/-! ## 4. The affine algebra/scheme equivalence -/

/-- The finite etale R'-algebra of global sections of an affine finite etale
model X.  Its underlying ring is the ring of X; its R'-algebra structure is the
global-sections map S1777AlgMap X, which is module-finite and etale by
S1777AlgMap_finite and S1777AlgMap_etale. -/
noncomputable def S1777SliceAlgebra (X : S1733Slice) : S1777Algᵒᵖ :=
  letI : Algebra S1777R (↥X.left.unop) := (S1777AlgMap X).hom.toAlgebra
  letI : Module.Finite S1777R (↥X.left.unop) := by
    rw [← RingHom.finite_algebraMap, RingHom.algebraMap_toAlgebra]
    exact S1777AlgMap_finite X
  letI : Algebra.Etale S1777R (↥X.left.unop) := by
    rw [← RingHom.etale_algebraMap, RingHom.algebraMap_toAlgebra]
    exact S1777AlgMap_etale X
  Opposite.op (CommAlgCat.FiniteEtale.of S1777R (↥X.left.unop))

/-- The algebra map of the global-sections algebra is the global-sections map. -/
lemma S1777SliceAlgebra_algebraMap (X : S1733Slice) :
    (algebraMap S1777R ↥(S1777SliceAlgebra X).unop : S1777R →+* ↥X.left.unop) =
      (S1777AlgMap X).hom :=
  RingHom.algebraMap_toAlgebra (S1777AlgMap X).hom

/-- The underlying ring of the model of the global-sections algebra is the ring
of X. -/
lemma S1777Obj_sliceAlgebra_left (X : S1733Slice) :
    (S1777Obj (S1777SliceAlgebra X)).left = X.left := rfl

/-- The structure morphism of the model of the global-sections algebra is the
original structure morphism of X. -/
lemma S1777Obj_sliceAlgebra_hom (X : S1733Slice) :
    (S1777Obj (S1777SliceAlgebra X)).hom = X.hom := by
  show Spec.map (CommRingCat.ofHom (algebraMap S1777R (↥(S1777SliceAlgebra X).unop))) =
    X.hom
  rw [S1777SliceAlgebra_algebraMap X, CommRingCat.ofHom_hom, S1777SpecMapAlgMap]

/-- Every affine finite etale model over Spec R' is the model of its finite etale
algebra of global sections. -/
noncomputable def S1777SliceIso (X : S1733Slice) :
    S1777Obj (S1777SliceAlgebra X) ≅ X :=
  MorphismProperty.CostructuredArrow.isoMk (Q := ⊤) (P := S1733FiniteEtale)
    (F := Scheme.Spec) (X := S1777Base) (Iso.refl _) (by trivial) (by trivial) (by
      show Scheme.Spec.map (Iso.refl _).hom ≫ X.hom =
        (S1777Obj (S1777SliceAlgebra X)).hom
      rw [Iso.refl_hom, Scheme.Spec.map_id, Category.id_comp, S1777Obj_sliceAlgebra_hom])

/-- **(M1), proved**: the algebra/scheme functor is essentially surjective.  This
is the affine half of representability of finite etale covers: every affine
finite etale scheme over Spec R' is the spectrum of the finite etale R'-algebra
of its global sections. -/
instance S1777SliceFunctor_essSurj : S1777SliceFunctor.EssSurj :=
  ⟨fun X => ⟨S1777SliceAlgebra X, ⟨S1777SliceIso X⟩⟩⟩

/-- **The affine algebra/scheme equivalence**: the affine finite etale slice
over Spec R' is equivalent to the opposite of the category of finite etale
R'-algebras.  This is the affine dictionary used by the stack-level comparison
below. -/
theorem S1777SliceEquiv :
    Nonempty (@CategoryTheory.Equivalence S1777Algᵒᵖ S1733Slice
      inferInstance inferInstance) := by
  haveI : S1777SliceFunctor.IsEquivalence :=
    ⟨inferInstance, inferInstance, S1777SliceFunctor_essSurj⟩
  exact ⟨S1777SliceFunctor.asEquivalence⟩

/-! ## 5. The stack-level target and the exact first missing theorem -/

/-- The target: the finite etale cover category of the S1726 orbicurve is
equivalent to the opposite of the finite etale R'-algebras. -/
def S1777TargetEquivalence : Prop :=
  Nonempty (@CategoryTheory.Equivalence S1728Cover S1777Algᵒᵖ
    S1728ActualCategory11 inferInstance)

/-- **The exact first missing theorem (M2)**: S1733's stack-level slice
comparison, i.e. the comparison between the actual stack-valued finite etale
covers and the affine finite etale slice.  It is the representability of finite
etale *covers* (stacks) over the affine base by affine finite etale schemes,
together with full faithfulness of that comparison; S1743 records it as
S1743CoverSliceComparison.  It is not constructed in the tree. -/
def S1777StackComparison : Prop := S1733CoverSliceEquivalence

theorem S1777StackComparison_iff :
    S1777StackComparison ↔ S1733CoverSliceEquivalence := Iff.rfl

/-- **The target equivalence is exactly the stack-level comparison.**  Since the
affine algebra/scheme dictionary is an equivalence (S1777SliceEquiv), composing
with it identifies the target with (M2); nothing is lost or added by the
reduction, and the residual gap is precisely (M2). -/
theorem S1777TargetEquivalence_iff :
    S1777TargetEquivalence ↔ S1777StackComparison := by
  obtain ⟨e⟩ := S1777SliceEquiv
  constructor
  · rintro ⟨f⟩
    exact ⟨f.trans e⟩
  · rintro ⟨f⟩
    exact ⟨f.trans e.symm⟩

/-- S1743's comparison form of (M2) supplies the stack comparison. -/
theorem S1777StackComparison_of_comparison (d : S1743CoverSliceComparison) :
    S1777StackComparison :=
  S1743CoverSliceEquivalence_of_comparison d

/-- **The target equivalence from S1743's missing comparison.**  This is the
single remaining input: an affine finite etale model of every cover, and the
identification of cover maps with maps of models (S1743CoverSliceComparison). -/
theorem S1777TargetEquivalence_of_comparison (d : S1743CoverSliceComparison) :
    S1777TargetEquivalence :=
  S1777TargetEquivalence_iff.mpr (S1777StackComparison_of_comparison d)

/-! ## 6. Checks -/

#check @S1777SliceFunctor
#check @S1777SliceFunctor_faithful
#check @S1777SliceFunctor_full
#check @S1777AlgMap
#check @S1777SpecMapAlgMap
#check @S1777AppTop_finite
#check @S1777AppTop_etale
#check @S1777AlgMap_finite
#check @S1777AlgMap_etale
#check @S1777SliceAlgebra
#check @S1777SliceAlgebra_algebraMap
#check @S1777Obj_sliceAlgebra_hom
#check @S1777SliceIso
#check @S1777SliceFunctor_essSurj
#check @S1777SliceEquiv
#check @S1777TargetEquivalence
#check @S1777StackComparison
#check @S1777TargetEquivalence_iff
#check @S1777TargetEquivalence_of_comparison

#print axioms S1777SliceFunctor_faithful
#print axioms S1777SliceFunctor_full
#print axioms S1777SpecMapAlgMap
#print axioms S1777AlgMap_finite
#print axioms S1777AlgMap_etale
#print axioms S1777SliceAlgebra_algebraMap
#print axioms S1777Obj_sliceAlgebra_hom
#print axioms S1777SliceFunctor_essSurj
#print axioms S1777SliceEquiv
#print axioms S1777TargetEquivalence_iff
#print axioms S1777TargetEquivalence_of_comparison

end LeanFormal.IUT.XiFPaper.S1777AffineCoverAlgebrasActual
