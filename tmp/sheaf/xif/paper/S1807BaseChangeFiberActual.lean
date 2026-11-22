/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF / S1807

# S1807 -- the four base change properties of S1769

S1769 reduced the fields 2--5 of `PreGaloisCategory.FiberFunctor (geometricFiber K)` to four
properties of Mathlib's base change functor
`bc K = CommAlgCat.FiniteEtale.baseChange K (AlgebraicClosure K)`:

* `BCPreservesPullbacks K`      : `PreservesLimitsOfShape WalkingCospan (bc K).op`,
* `BCPreservesFiniteProducts K` : `PreservesFiniteProducts (bc K)`,
* `BCPreservesEpis K`           : `Functor.PreservesEpimorphisms (bc K).op`,
* `BCPreservesQuotients K`      : `forall G [Group G] [Finite G],
                                     PreservesColimitsOfShape (SingleObj G) (bc K).op`.

The definitions below are verbatim copies of the four statements of S1769 (they are repeated
here only so that this file has no dependency on the not-yet-built `S1769` olean).

## What is proved here

Three of the four are proved unconditionally, for every field `K`:

* `bcPreservesFiniteProducts` (`BCPreservesFiniteProducts`),
* `bcPreservesEpis`           (`BCPreservesEpis`),
* `bcPreservesQuotients`      (`BCPreservesQuotients`).

They are all consequences of the stronger theorem

  `bc_preservesFiniteLimits : PreservesFiniteLimits (bc K)`,

proved here from scratch:

1. finite products: the product of finite etale algebras is the `Pi` algebra (`piFan`,
   `piFanIsLimit`), and `Kbar (x)_K -` carries it to the `Pi` algebra over `Kbar`
   (`Algebra.TensorProduct.piRight`, see `piRight_comp_eval`);
2. equalizers: the equalizer of `f g : A ⟶ B` is the subalgebra `AlgHom.equalizer f g`
   (`eqFork`, `eqForkIsLimit`; finiteness and etaleness of this subalgebra are
   `Module.Finite` for a subalgebra of a finite algebra over a field and S1770's
   `etale_subalgebra`), and `Kbar (x)_K -` carries it to the equalizer of the base changes
   (`AlgHom.tensorEqualizerEquiv`, see `tensorEqualizer_comp_eqι`);
3. flatness of `Kbar` over `K` (`Module.Flat K Kbar`, an instance for a field) is what makes
   the equalizer statement true.

Consequences:

* `bc_preservesFiniteLimits` gives all finite limits, in particular `WalkingCospan` and
  `(SingleObj G)^op`-shaped limits;
* `PreservesEpimorphisms (bc K).op` follows because `bc K` preserves monomorphisms:
  for a mono `f` the pullback of `f` along itself is the (iso) diagonal, and pullback
  preservation transports it;
* `PreservesColimitsOfShape (SingleObj G) (bc K).op` follows from
  `preservesColimitsOfShape_op` and the fact that `(SingleObj G)^op` is a finite shape.

## Exact first missing

The first missing item, in the order of the fields of S1769, is `BCPreservesPullbacks K`
(equivalently: `bc K` preserves pushouts, i.e. `PreservesColimitsOfShape WalkingSpan (bc K)`).
It is *not* a consequence of `PreservesFiniteLimits`: pushouts are colimits.

Concretely, the single missing mathematical input is the following coherence, which Mathlib
does not contain as a single statement: for a span `A --f--> B`, `A --g--> C` of finite etale
`K`-algebras (with `A` acting on `B`, `C` through `f`, `g`), an isomorphism of
`Kbar`-algebras

  `Kbar ⊗[K] (B ⊗[A] C) ≃ₐ[Kbar] (Kbar ⊗[K] B) ⊗[Kbar ⊗[K] A] (Kbar ⊗[K] C)`

compatible with the four canonical maps, where `B ⊗[A] C` is the pushout of `f`, `g` in
`CommAlgCat K` (S1745's `tensorCocone`).  Equivalently (and this is the form in which it can be
fed to `PushoutCocone.IsColimit.mk`), the universal property

  `Hom_Kbar(Kbar ⊗[K] (B ⊗[A] C), D) ≃ {(u : Kbar ⊗[K] B →ₐ[Kbar] D), (v : Kbar ⊗[K] C →ₐ[Kbar] D)
      // u ∘ (id ⊗ f) = v ∘ (id ⊗ g)}`

for every finite etale `Kbar`-algebra `D`.

Mathlib's `Algebra.IsPushout` API (`Mathlib/RingTheory/IsTensorProduct.lean`) contains the
closest available material: `Algebra.IsPushout.tensorProduct_tensorProduct` (the square
`A → B`, `A → A ⊗[R] S`, `B → B ⊗[R] S` is a pushout), `IsPushout.cancelBaseChangeAlg`
(`B ⊗[A] C ≃ₐ[S] S ⊗[R] C` when `B = S ⊗[R] A`) and `Algebra.IsPushout.comp_iff`
(cancellation of a left pushout square in a rectangle).  Deriving the coherence above from these
is the remaining formal work; no `sorry`-free proof of it exists in this repository yet.

The other (purely formal) ingredients *are* available: S1745's pushout cocone and its colimit
property in `CommAlgCat` (`tensorCocone`, `tensorCocone_isColimit`), the closure of
`CommAlgCat.finiteEtale K` under `WalkingSpan`-colimits
(`isClosedUnderColimitsOfShape_walkingSpan`), and the shape equivalence
`walkingCospanOpEquiv : WalkingCospanᵒᵖ ≌ WalkingSpan`.

No `sorry`, `admit`, new axiom or weakened statement occurs in this file.
-/
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Descent
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.Algebra.Category.Ring.Under.Limits
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Etale.Field
import tmp.sheaf.xif.paper.S1745FiniteEtaleLimitsActual
import tmp.sheaf.xif.paper.S1770FiniteEtaleFixedPointsActual

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace S1807

abbrev Kbar (K : Type) [Field K] : Type := AlgebraicClosure K

abbrev bc (K : Type) [Field K] :
    CommAlgCat.FiniteEtale.{0} K ⥤ CommAlgCat.FiniteEtale.{0} (Kbar K) :=
  CommAlgCat.FiniteEtale.baseChange K (Kbar K)

instance instFlatKbar (K : Type) [Field K] : Module.Flat K (Kbar K) := inferInstance

/-! ### 1. Finite products -/

section Pi

variable (R : Type) [CommRing R]

noncomputable def piFan (J : Type) [Fintype J] (A : J → CommAlgCat.FiniteEtale.{0} R) :
    Fan A :=
  Fan.mk (CommAlgCat.FiniteEtale.of R (∀ j, (A j : Type)))
    (fun j => CommAlgCat.FiniteEtale.ofHom (Pi.evalAlgHom R (fun j => (A j : Type)) j))

@[simp] lemma piFan_proj_apply (J : Type) [Fintype J] (A : J → CommAlgCat.FiniteEtale.{0} R)
    (j : J) (x : (piFan R J A).pt) : ((piFan R J A).proj j).hom.hom x = x j := rfl

noncomputable def piFanIsLimit (J : Type) [Fintype J] (A : J → CommAlgCat.FiniteEtale.{0} R) :
    IsLimit (piFan R J A) := by
  refine Fan.IsLimit.mk _ (fun s => CommAlgCat.FiniteEtale.ofHom (AlgHom.pi fun j => (s.proj j).hom.hom)) ?_ ?_
  · intro s j
    ext x
    rfl
  · intro s m hm
    ext x
    funext j
    exact congrArg (fun f => ((f : s.pt ⟶ A j)).hom.hom x) (hm j)

end Pi

section PiBC

variable {K : Type} [Field K]

lemma piRight_comp_eval {J : Type} [Fintype J] [DecidableEq J]
    (A : J → CommAlgCat.FiniteEtale.{0} K) (j : J) :
    (Algebra.TensorProduct.map (AlgHom.id (Kbar K) (Kbar K))
        (Pi.evalAlgHom K (fun i => (A i : Type)) j) :
      Kbar K ⊗[K] (∀ i, (A i : Type)) →ₐ[Kbar K] Kbar K ⊗[K] (A j : Type))
      = (Pi.evalAlgHom (Kbar K) (fun i => Kbar K ⊗[K] (A i : Type)) j).comp
          (Algebra.TensorProduct.piRight K (Kbar K) (Kbar K) (fun i => (A i : Type))).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro a f
  simp [Algebra.TensorProduct.piRight_tmul]

noncomputable def bc_piFan_isLimit {J : Type} [Fintype J]
    (A : J → CommAlgCat.FiniteEtale.{0} K) :
    IsLimit ((bc K).mapCone (piFan K J A)) := by
  classical
  have key : IsLimit (Fan.mk ((bc K).obj (piFan K J A).pt)
      (fun j => (bc K).map ((piFan K J A).proj j))) := by
    have e : (Fan.mk ((bc K).obj (piFan K J A).pt)
        (fun j => (bc K).map ((piFan K J A).proj j))) ≅
        piFan (Kbar K) J (fun j => (bc K).obj (A j)) := by
      refine Fan.ext (CommAlgCat.FiniteEtale.isoMk (Algebra.TensorProduct.piRight K (Kbar K) (Kbar K) (fun j => (A j : Type)))) ?_
      intro j
      apply ObjectProperty.hom_ext
      apply CommAlgCat.hom_ext
      exact piRight_comp_eval A j
    exact IsLimit.ofIsoLimit (piFanIsLimit (Kbar K) J (fun j => (bc K).obj (A j))) e.symm
  exact (isLimitMapConeFanMkEquiv (bc K) A (fun j => (piFan K J A).proj j)).invFun key

instance bc_preservesFiniteProducts (K : Type) [Field K] :
    PreservesFiniteProducts (bc K) where
  preserves n := by
    haveI : ∀ (f : Fin n → CommAlgCat.FiniteEtale.{0} K),
        PreservesLimit (Discrete.functor f) (bc K) :=
      fun f => preservesLimit_of_preserves_limit_cone (piFanIsLimit K (Fin n) f)
        (bc_piFan_isLimit f)
    exact preservesLimitsOfShape_of_discrete (bc K)

end PiBC

/-! ### 2. Equalizers -/

section Eq

variable (R : Type) [Field R]

noncomputable def eqPt {A B : CommAlgCat.FiniteEtale.{0} R} (f g : A ⟶ B) :
    CommAlgCat.FiniteEtale.{0} R :=
  letI : Algebra.Etale R ↥(AlgHom.equalizer f.hom.hom g.hom.hom) :=
    S1770.etale_subalgebra (AlgHom.equalizer f.hom.hom g.hom.hom)
  CommAlgCat.FiniteEtale.of R ↥(AlgHom.equalizer f.hom.hom g.hom.hom)

noncomputable def eqι {A B : CommAlgCat.FiniteEtale.{0} R} (f g : A ⟶ B) :
    eqPt R f g ⟶ A :=
  ObjectProperty.homMk (CommAlgCat.ofHom (AlgHom.equalizer f.hom.hom g.hom.hom).val)

theorem eqFork_condition {A B : CommAlgCat.FiniteEtale.{0} R} (f g : A ⟶ B) :
    eqι R f g ≫ f = eqι R f g ≫ g := by
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  exact x.property

noncomputable def eqFork {A B : CommAlgCat.FiniteEtale.{0} R} (f g : A ⟶ B) : Fork f g :=
  Fork.ofι (eqι R f g) (eqFork_condition R f g)

noncomputable def eqForkIsLimit {A B : CommAlgCat.FiniteEtale.{0} R} (f g : A ⟶ B) :
    IsLimit (eqFork R f g) := by
  refine Fork.IsLimit.mk (eqFork R f g) ?_ ?_ ?_
  · intro s
    exact ObjectProperty.homMk (CommAlgCat.ofHom (AlgHom.codRestrict (Fork.ι s).hom.hom
      (AlgHom.equalizer f.hom.hom g.hom.hom)
      (fun x => congrArg (fun (φ : s.pt ⟶ B) => φ.hom.hom x) (Fork.condition s))))
  · intro s
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
    apply Subtype.ext
    exact congrArg (fun (φ : s.pt ⟶ A) => φ.hom.hom x) hm

instance hasEqualizersFiniteEtale (R : Type) [Field R] :
    HasEqualizers (CommAlgCat.FiniteEtale.{0} R) := by
  haveI : ∀ {X Y : CommAlgCat.FiniteEtale.{0} R} {f g : X ⟶ Y}, HasLimit (parallelPair f g) :=
    fun {X Y} {f g} => HasLimit.mk ⟨eqFork R f g, eqForkIsLimit R f g⟩
  exact hasEqualizers_of_hasLimit_parallelPair (CommAlgCat.FiniteEtale.{0} R)

end Eq

section EqBC

variable {K : Type} [Field K]

lemma tensorEqualizer_comp_eqι {A B : CommAlgCat.FiniteEtale.{0} K} (f g : A ⟶ B) :
    (AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id (Kbar K) (Kbar K))
          (CommAlgCat.Hom.hom f.hom))
        (Algebra.TensorProduct.map (AlgHom.id (Kbar K) (Kbar K))
          (CommAlgCat.Hom.hom g.hom))).val.comp
      (AlgHom.tensorEqualizerEquiv (R := K) (S := Kbar K) (T := Kbar K)
        (CommAlgCat.Hom.hom f.hom) (CommAlgCat.Hom.hom g.hom)).toAlgHom
      = Algebra.TensorProduct.map (AlgHom.id (Kbar K) (Kbar K))
          (AlgHom.equalizer (CommAlgCat.Hom.hom f.hom) (CommAlgCat.Hom.hom g.hom)).val := by
  apply Algebra.TensorProduct.ext'
  intro a y
  simp

noncomputable def bc_eqFork_isLimit {A B : CommAlgCat.FiniteEtale.{0} K} (f g : A ⟶ B) :
    IsLimit ((bc K).mapCone (eqFork K f g)) := by
  have hbase : IsLimit (eqFork (Kbar K) ((bc K).map f) ((bc K).map g)) :=
    eqForkIsLimit (Kbar K) ((bc K).map f) ((bc K).map g)
  have hcond : (bc K).map (eqι K f g) ≫ (bc K).map f = (bc K).map (eqι K f g) ≫ (bc K).map g := by
    rw [← Functor.map_comp, ← Functor.map_comp, eqFork_condition]
  have e : (Fork.ofι ((bc K).map (eqι K f g)) hcond) ≅
      (eqFork (Kbar K) ((bc K).map f) ((bc K).map g)) :=
    Fork.ext (CommAlgCat.FiniteEtale.isoMk (AlgHom.tensorEqualizerEquiv (R := K) (S := Kbar K)
      (T := Kbar K) f.hom.hom g.hom.hom)) (by
        apply ObjectProperty.hom_ext
        apply CommAlgCat.hom_ext
        exact tensorEqualizer_comp_eqι f g)
  have h1 : IsLimit (Fork.ofι ((bc K).map (eqι K f g)) hcond) := IsLimit.ofIsoLimit hbase e.symm
  exact (isLimitMapConeForkEquiv (bc K) (eqFork_condition K f g)).invFun h1

instance bc_preservesParallelPair (K : Type) [Field K] {A B : CommAlgCat.FiniteEtale.{0} K}
    (f g : A ⟶ B) : PreservesLimit (parallelPair f g) (bc K) :=
  preservesLimit_of_preserves_limit_cone (eqForkIsLimit K f g) (bc_eqFork_isLimit f g)

instance bc_preservesEqualizers (K : Type) [Field K] :
    PreservesLimitsOfShape WalkingParallelPair (bc K) where
  preservesLimit {X} := preservesLimit_of_iso_diagram _ (diagramIsoParallelPair X).symm

instance bc_preservesFiniteLimits (K : Type) [Field K] : PreservesFiniteLimits (bc K) :=
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts (bc K)

end EqBC

/-! ### 3. Pullbacks and monomorphisms -/

/-- A monomorphism has a pullback along itself: the identity square is limiting. -/
instance monoSelfPullback {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) [Mono f] :
    HasPullback f f := by
  refine ⟨⟨PullbackCone.mk (𝟙 X) (𝟙 X) (by simp), ?_⟩⟩
  refine PullbackCone.IsLimit.mk _ (fun s => s.fst) ?_ ?_ ?_
  · intro s
    simp
  · intro s
    have h : s.fst = s.snd := (cancel_mono f).mp s.condition
    simp [h]
  · intro s m hm1 hm2
    simpa using hm1

section Mono

variable {K : Type} [Field K]

instance bc_preservesMonomorphisms (K : Type) [Field K] :
    Functor.PreservesMonomorphisms (bc K) where
  preserves {X Y} f hf := by
    haveI : Mono f := hf
    haveI : HasPullback f f := monoSelfPullback f
    haveI : HasPullback ((bc K).map f) ((bc K).map f) :=
      hasPullback_of_preservesPullback (bc K) f f
    haveI : IsIso (pullback.fst f f) := isIso_fst_of_mono f
    haveI : IsIso (pullback.fst ((bc K).map f) ((bc K).map f)) := by
      rw [← PreservesPullback.iso_inv_fst]
      exact IsIso.comp_isIso
    exact (pullback.diagonal_isKernelPair ((bc K).map f)).mono_of_isIso_fst

/-- **The third base change condition of S1769**: the opposite of base change preserves
epimorphisms, i.e. base change preserves monomorphisms. -/
instance bc_op_preservesEpimorphisms (K : Type) [Field K] :
    Functor.PreservesEpimorphisms (bc K).op where
  preserves {X Y} f hf := by
    haveI hmono : Mono f.unop := (op_epi_iff f.unop).mp (by simpa using hf)
    haveI : Mono ((bc K).map f.unop) := inferInstance
    exact (op_epi_iff ((bc K).map f.unop)).mpr inferInstance

end Mono

/-! ### 4. Quotients by finite groups -/

section Quotients

variable {K : Type} [Field K]

instance finCategorySingleObjOp (G : Type) [Group G] [Finite G] :
    FinCategory (SingleObj G)ᵒᵖ := by
  letI : Fintype G := Fintype.ofFinite G
  infer_instance

instance bc_preservesColimitsOfShapeSingleObj (G : Type) [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) (bc K).op := by
  haveI : PreservesLimitsOfShape (SingleObj G)ᵒᵖ (bc K) := inferInstance
  exact preservesColimitsOfShape_op (J := SingleObj G) (bc K)

end Quotients

/-! ### 5. The four conditions of S1769 -/

/-- **Condition for field 2 (S1769)**: base change preserves pushouts. -/
def BCPreservesPullbacks (K : Type) [Field K] : Prop :=
  PreservesLimitsOfShape WalkingCospan (bc K).op

/-- **Condition for field 3 (S1769)**: base change preserves finite products.  PROVED. -/
def BCPreservesFiniteProducts (K : Type) [Field K] : Prop :=
  PreservesFiniteProducts (bc K)

/-- **Condition for field 4 (S1769)**: the opposite of base change preserves epimorphisms.
PROVED. -/
def BCPreservesEpis (K : Type) [Field K] : Prop :=
  Functor.PreservesEpimorphisms (bc K).op

/-- **Condition for field 5 (S1769)**: base change preserves quotients by finite groups.
PROVED. -/
def BCPreservesQuotients (K : Type) [Field K] : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PreservesColimitsOfShape (SingleObj G) (bc K).op

theorem bcPreservesFiniteProducts (K : Type) [Field K] : BCPreservesFiniteProducts K :=
  bc_preservesFiniteProducts K

theorem bcPreservesEpis (K : Type) [Field K] : BCPreservesEpis K :=
  bc_op_preservesEpimorphisms K

theorem bcPreservesQuotients (K : Type) [Field K] : BCPreservesQuotients K :=
  fun G _ _ => bc_preservesColimitsOfShapeSingleObj G

/-! ### 6. Axiom audit -/

#print axioms S1807.bc_preservesFiniteLimits
#print axioms S1807.bc_preservesFiniteProducts
#print axioms S1807.bc_preservesMonomorphisms
#print axioms S1807.bc_op_preservesEpimorphisms
#print axioms S1807.bc_preservesColimitsOfShapeSingleObj
#print axioms S1807.bcPreservesFiniteProducts
#print axioms S1807.bcPreservesEpis
#print axioms S1807.bcPreservesQuotients

end S1807