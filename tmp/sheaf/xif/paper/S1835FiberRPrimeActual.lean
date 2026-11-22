/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1835
-/
import tmp.sheaf.xif.paper.S1830G2G3RPrimeActual
import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.RingTheory.Etale.Field
import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Equalizer

/-!
# S1835: the six fields of the geometric fibre functor over the coordinate ring R'

S1825 reduced the Galois structure on the actual small cover category
`S1809CoverCategory01` to three inputs: the affine bridge, the `R'`-level (G2)/(G3)
(discharged by S1830), and the six fields of the geometric fibre functor at the geometric
point `(0,0)`.  This file attacks the third input.

## Setting

* `R' = S1779R = S1726CoordinateRing`, the coordinate ring of the affine punctured
  elliptic curve `E' minus O` over the number field `F' = S1726K`;
* `Omega = AlgebraicClosure F'`, with the `R'`-algebra structure given by the actual
  geometric point `(0,0)` (`S1779Point`, `S1779PointClosureAlgebra`);
* `S1835Fiber = S1779GeometricFiber = CommAlgCat.FiniteEtale.fiber R' Omega`, Mathlib's
  genuine fibre functor `A ↦ Hom_{R'}(A, Omega)`;
* `S1835BC = CommAlgCat.FiniteEtale.baseChange R' Omega`, Mathlib's base change.

Mathlib's `fiberIsoBaseChangeFiber` gives the unconditional comparison
`S1835FiberIso : S1835Fiber ≅ S1835BC.op ⋙ CommAlgCat.FiniteEtale.fiber Omega Omega`,
and `fiber Omega Omega` is an equivalence (`equivOfIsSepClosed`), so every
preservation/reflection property of the fibre functor follows from the same property of
base change.  This is the reduction used for fields 4--6 (S1769's reduction, at `R'`).

## What is proved here, unconditionally

* **Field 1** (`preservesTerminalObjects`): `S1835PreservesTerminalObjects`.  The fibre of
  the terminal object is `Hom_{R'}(R', Omega)`, a one-point type.
* **Field 2** (`preservesPullbacks`): `S1835PreservesPullbacks`.  It is deduced from
  `S1835BCPreservesPullbacks`, i.e. from the fact that base change preserves pushouts of
  finite etale algebras.  The proof is the adjunction "extension of scalars is left adjoint
  to restriction of scalars" (`S1835Adj`), which is S1826's argument, re-proved for an
  arbitrary commutative base ring and an arbitrary commutative algebra; it never uses that
  `R'` is a field.  Over a field this was S1769/S1807's *first missing* condition; over
  `R'` it is unconditional.
* **Field 3** (`preservesFiniteCoproducts`): `S1835PreservesFiniteCoproducts`, from
  `S1835BCPreservesFiniteProducts` (tensor product commutes with finite products of
  algebras), which is S1807's product computation re-proved for an arbitrary commutative
  base ring (`S1835Pi`).

## The exact remaining input: fields 4, 5, 6

They are reduced, without weakening or change of statement, to three properties of
`S1835BC = baseChange R' Omega`:

| field | condition (a Lean `Prop`) | concrete description |
|---|---|---|
| 4 `preservesEpis` | `S1835BCPreservesEpis : PreservesEpimorphisms S1835BC.op` | `S1835BCInjectiveOnMonos`: for every mono `f : X ⟶ Y` of finite etale `R'`-algebras, `Omega (x)_{R'} X → Omega (x)_{R'} Y` is injective |
| 5 `preservesQuotientsByFiniteGroups` | `S1835BCPreservesQuotients : ∀ G, PreservesColimitsOfShape (SingleObj G) S1835BC.op` | fixed points commute with base change, `Omega (x)_{R'} A^G ≅ (Omega (x)_{R'} A)^G` (not separately formalized here) |
| 6 `reflectsIsos` | `S1835BCReflectsIsos : S1835BC.op.ReflectsIsomorphisms` | `S1835BCReflectsIsosConcrete` (equivalent, kernel-checked) |

`S1835BCPreservesEpis_of_injectiveOnMonos` proves that the concrete form of field 4 implies
field 4 verbatim; `S1835BCReflectsIsos_iff_concrete` proves that field 6 is exactly its
concrete form.  `S1835FiberFunctorOf` assembles the full six-field
`PreGaloisCategory.FiberFunctor S1779GeometricFiber` from precisely these three conditions
(together with S1830's unconditional `PreGaloisCategory`).

## Exact first missing

**Field 4, `S1835BCPreservesEpis`** (equivalently the concrete
`S1835BCInjectiveOnMonos`).  In the order of the class fields, fields 1--3 are proved
above, so this is the first field that is not discharged in this file.

## Why the field-case proofs (S1769/S1807/S1826/S1834) do not transfer

Over a field `K`, all four base-change conditions are proved from flatness/faithful
flatness of `K → AlgebraicClosure K` (S1807, S1826), and S1834 assembles the unconditional
`GaloisCategory`.  Over `R'` the geometric point `(0,0)` is a **closed** point: the
structure map `R' → Omega` factors through the residue field `F' = R'/m` of `(0,0)`
(`S1779Point` is evaluation at `(0,0)`).  Hence:

* mathematically, `Omega` is not faithfully flat over `R'` (the maximal ideal of the closed
  point acts as zero on `Omega`) and not flat over `R'` either (neither statement is
  formalized in this file), so S1769's
  `Module.FaithfullyFlat.lTensor_bijective_iff_bijective` argument for field 6 does not
  apply;
* base change to a non-flat algebra does not preserve injectivity of arbitrary maps;
* fixed points need not commute with such a base change.

Mathematically, the six-field statement at a closed geometric point of a *connected* scheme
is the SGA1 theorem that every geometric point of a connected scheme gives a fibre functor;
the tree has the affine equivalence `(FiniteEtale R')^op ≌ FiniteEtaleCover (Spec R')`
(S1799) but not the SGA1 connectedness/Galois-category theory of `FiniteEtaleCover`.
Neither that theory nor the algebra behind the three conditions above is available, so they
are recorded as exact residuals and not assumed.

## Verification (session S1835, 2026-11-01)

Compiled with

    lake env lean -j1 -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1835FiberRPrimeActual.olean
      tmp/sheaf/xif/paper/S1835FiberRPrimeActual.lean

-> EXIT=0, no errors, no `sorryAx`; every `#print axioms` below prints only
`[propext, Classical.choice, Quot.sound]`.

## Honest boundary

No `sorry`, `admit`, new axiom, `Shrink`, `ULift` or `PUnit` occurs in this file.
Every declaration depends only on `propext`, `Classical.choice` and `Quot.sound`
(`#print axioms` at the end).  Fields 1--3 are proved; fields 4--6 are *not* proved, only
reduced to the exact statements `S1835BCPreservesEpis`, `S1835BCPreservesQuotients`,
`S1835BCReflectsIsos` (with the concrete forms above).  Combined with S1830's
`PreGaloisCategory S1779AlgR` and S1825's assembly, the only remaining algebra-side input for
`GaloisCategory (FiniteEtale R')^op` is these three conditions.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1835FiberRPrimeActual

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual.S1779FiniteEtaleClosure
open LeanFormal.IUT.XiFPaper.S1830G2G3RPrimeActual

/-- The coordinate ring R'. -/
abbrev S1835R : Type := S1779R

/-- The base field F'. -/
abbrev S1835K : Type := S1779K

/-- The geometric point field Omega = algebraic closure of F'. -/
abbrev S1835Omega : Type := AlgebraicClosure S1779K

attribute [local instance] S1779PointClosureAlgebra

/-- The corrected algebra side. -/
abbrev S1835AlgR : Type 1 := S1779AlgR

/-- Base change along R' -> Omega. -/
abbrev S1835BC : CommAlgCat.FiniteEtale.{0} S1779R ⥤ CommAlgCat.FiniteEtale.{0} S1835Omega :=
  CommAlgCat.FiniteEtale.baseChange S1779R S1835Omega

/-- The field-level fibre functor over Omega. -/
abbrev S1835E : (CommAlgCat.FiniteEtale.{0} S1835Omega)ᵒᵖ ⥤ FintypeCat.{0} :=
  CommAlgCat.FiniteEtale.fiber S1835Omega S1835Omega

/-- The geometric fibre functor at (0,0)/AlgebraicClosure F'. -/
abbrev S1835Fiber : S1779AlgR ⥤ FintypeCat.{0} := S1779GeometricFiber

/-- The base-change comparison of Mathlib. -/
noncomputable def S1835FiberIso : S1835Fiber ≅ (S1835BC).op ⋙ S1835E :=
  CommAlgCat.FiniteEtale.fiberIsoBaseChangeFiber (R := S1779R) (Ω := S1835Omega) (S := S1835Omega)

/-- The field-level fibre functor is an equivalence. -/
noncomputable def S1835EEquiv : (CommAlgCat.FiniteEtale.{0} S1835Omega)ᵒᵖ ≌ FintypeCat.{0} :=
  CommAlgCat.FiniteEtale.equivOfIsSepClosed S1835Omega

example : S1835E.IsEquivalence := inferInstance

/-! ## Field 1: the terminal object -/

section Field1

/-- The terminal object of `S1779AlgR` is the opposite of R' itself (S1779). -/
noncomputable def S1835TerminalIsoSelf [PreGaloisCategory S1779AlgR] :
    (⊤_ S1779AlgR) ≅ Opposite.op (CommAlgCat.FiniteEtale.of S1779R S1779R) :=
  terminalIsTerminal.uniqueUpToIso S1779FiniteEtaleAlg.isTerminal_self

theorem S1835TerminalObjSubsingleton [PreGaloisCategory S1779AlgR] :
    Subsingleton ((S1835Fiber).obj (⊤_ S1779AlgR) : Type) := by
  let e := (S1835Fiber).mapIso (S1835TerminalIsoSelf)
  let ee : ((S1835Fiber).obj (⊤_ S1779AlgR) : Type) ≃
      ((S1835Fiber).obj (Opposite.op (CommAlgCat.FiniteEtale.of S1779R S1779R)) : Type) :=
    FintypeCat.equivEquivIso.symm e
  haveI : Subsingleton ((S1835Fiber).obj
      (Opposite.op (CommAlgCat.FiniteEtale.of S1779R S1779R)) : Type) := by
    change Subsingleton (S1779R →ₐ[S1779R] S1835Omega)
    infer_instance
  refine ⟨fun x y => ?_⟩
  apply ee.injective
  exact Subsingleton.elim _ _

theorem S1835TerminalObjNonempty [PreGaloisCategory S1779AlgR] :
    Nonempty ((S1835Fiber).obj (⊤_ S1779AlgR) : Type) := by
  let e := (S1835Fiber).mapIso (S1835TerminalIsoSelf)
  let ee : ((S1835Fiber).obj (⊤_ S1779AlgR) : Type) ≃
      ((S1835Fiber).obj (Opposite.op (CommAlgCat.FiniteEtale.of S1779R S1779R)) : Type) :=
    FintypeCat.equivEquivIso.symm e
  exact ⟨ee.symm (Algebra.ofId S1779R S1835Omega)⟩

noncomputable def S1835TerminalObjIsTerminal [PreGaloisCategory S1779AlgR] :
    IsTerminal ((S1835Fiber).obj (⊤_ S1779AlgR)) := by
  haveI : Subsingleton ((S1835Fiber).obj (⊤_ S1779AlgR) : Type) :=
    S1835TerminalObjSubsingleton
  haveI : Nonempty ((S1835Fiber).obj (⊤_ S1779AlgR) : Type) := S1835TerminalObjNonempty
  refine IsTerminal.ofUniqueHom (fun Y => FintypeCat.homMk (fun _ => Classical.arbitrary _)) ?_
  intro Y m
  apply FintypeCat.hom_ext
  intro y
  exact Subsingleton.elim _ _

/-- **Field 1** of `PreGaloisCategory.FiberFunctor`: the geometric fibre functor at
(0,0)/AlgebraicClosure F' preserves terminal objects, over the coordinate ring R'. -/
theorem S1835PreservesTerminalObjects [PreGaloisCategory S1779AlgR] :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (S1835Fiber) := by
  have h : PreservesLimit (Functor.empty.{0} S1779AlgR) (S1835Fiber) := by
    let e : (S1835Fiber).obj (⊤_ S1779AlgR) ≅ ⊤_ FintypeCat :=
      (S1835TerminalObjIsTerminal).uniqueUpToIso terminalIsTerminal
    exact preservesTerminal_of_iso (S1835Fiber) e
  haveI := h
  exact preservesLimitsOfShape_pempty_of_preservesTerminal (G := S1835Fiber)

end Field1


/-! ## Field 2: base change preserves pushouts, hence the fibre functor preserves pullbacks

The whole content is the adjunction "extension of scalars `T (x)_R -` is left adjoint to
restriction of scalars" on the ambient categories of commutative algebras (S1826 proved it
for a field `K`); it is completely insensitive to `R` being a field, so it is reproved
here for the coordinate ring `R'` and `Omega = AlgebraicClosure F'`. -/

namespace S1835Adj

/-! ### 1. Extension and restriction of scalars on CommAlgCat -/

section ChangeOfRings

variable {R : Type} [CommRing R] {T : Type} [CommRing T] [Algebra R T]

/-- Extension of scalars A |-> T (x)_R A, as a functor on all commutative R-algebras. -/
noncomputable def extendScalars : CommAlgCat.{0} R ⥤ CommAlgCat.{0} T where
  obj A := CommAlgCat.of T (T ⊗[R] (A : Type))
  map {A B} f :=
    CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id T T) f.hom)
  map_id A := by
    ext x
    simp
  map_comp {A B C} f g := by
    ext x
    simp

/-- Restriction of scalars A |-> A, viewing a T-algebra as an R-algebra. -/
noncomputable def restrictScalars : CommAlgCat.{0} T ⥤ CommAlgCat.{0} R where
  obj A :=
    letI : Algebra R (A : Type) :=
      ((algebraMap T (A : Type)).comp (algebraMap R T)).toAlgebra
    letI : IsScalarTower R T (A : Type) := IsScalarTower.of_algebraMap_eq' rfl
    CommAlgCat.of R (A : Type)
  map {A B} f :=
    letI : Algebra R (A : Type) :=
      ((algebraMap T (A : Type)).comp (algebraMap R T)).toAlgebra
    letI : IsScalarTower R T (A : Type) := IsScalarTower.of_algebraMap_eq' rfl
    letI : Algebra R (B : Type) :=
      ((algebraMap T (B : Type)).comp (algebraMap R T)).toAlgebra
    letI : IsScalarTower R T (B : Type) := IsScalarTower.of_algebraMap_eq' rfl
    CommAlgCat.ofHom (f.hom.restrictScalars R)
  map_id A := by
    ext x
    rfl
  map_comp {A B C} f g := by
    ext x
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The hom-set equivalence of the adjunction extendScalars -| restrictScalars.
A T-algebra map T (x)_R X -> Y is the same as an R-algebra map X -> Y, by
Mathlib's Algebra.TensorProduct.liftEquivRight. -/
noncomputable def homEquiv (X : CommAlgCat.{0} R) (Y : CommAlgCat.{0} T) :
    (extendScalars.obj X ⟶ Y) ≃ (X ⟶ restrictScalars.obj Y) where
  toFun f :=
    letI : Algebra R (Y : Type) :=
      ((algebraMap T (Y : Type)).comp (algebraMap R T)).toAlgebra
    letI : IsScalarTower R T (Y : Type) := IsScalarTower.of_algebraMap_eq' rfl
    CommAlgCat.ofHom ((Algebra.TensorProduct.liftEquivRight (R := R) (S := T)
      (B := (X : Type)) (C := (Y : Type))).symm f.hom)
  invFun g :=
    letI : Algebra R (Y : Type) :=
      ((algebraMap T (Y : Type)).comp (algebraMap R T)).toAlgebra
    letI : IsScalarTower R T (Y : Type) := IsScalarTower.of_algebraMap_eq' rfl
    CommAlgCat.ofHom ((Algebra.TensorProduct.liftEquivRight (R := R) (S := T)
      (B := (X : Type)) (C := (Y : Type))) g.hom)
  left_inv f := by
    letI : Algebra R (Y : Type) :=
      ((algebraMap T (Y : Type)).comp (algebraMap R T)).toAlgebra
    letI : IsScalarTower R T (Y : Type) := IsScalarTower.of_algebraMap_eq' rfl
    apply CommAlgCat.hom_ext
    rw [CommAlgCat.hom_ofHom, CommAlgCat.hom_ofHom, Equiv.apply_symm_apply]
  right_inv g := by
    letI : Algebra R (Y : Type) :=
      ((algebraMap T (Y : Type)).comp (algebraMap R T)).toAlgebra
    letI : IsScalarTower R T (Y : Type) := IsScalarTower.of_algebraMap_eq' rfl
    apply CommAlgCat.hom_ext
    rw [CommAlgCat.hom_ofHom, CommAlgCat.hom_ofHom, Equiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
/-- **Extension of scalars is left adjoint to restriction of scalars.** The two naturality
squares are checked on pure tensors. -/
noncomputable def adj : extendScalars (R := R) (T := T) ⊣ restrictScalars (R := R) (T := T) :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv
    homEquiv_naturality_left_symm := by
      intro X' X Y f g
      letI : Algebra R (Y : Type) :=
        ((algebraMap T (Y : Type)).comp (algebraMap R T)).toAlgebra
      letI : IsScalarTower R T (Y : Type) := IsScalarTower.of_algebraMap_eq' rfl
      change CommAlgCat.ofHom (Algebra.TensorProduct.liftEquivRight (R := R) (S := T)
          (B := (X' : Type)) (C := (Y : Type)) (CommAlgCat.Hom.hom (f ≫ g)))
        = extendScalars.map f ≫ CommAlgCat.ofHom (Algebra.TensorProduct.liftEquivRight (R := R)
            (S := T) (B := (X : Type)) (C := (Y : Type)) (CommAlgCat.Hom.hom g))
      apply CommAlgCat.hom_ext
      apply (Algebra.TensorProduct.liftEquivRight (R := R) (S := T)
        (B := (X' : Type)) (C := (Y : Type))).symm.injective
      ext x
      simp [extendScalars, CommAlgCat.hom_comp, AlgHom.comp_apply,
        Algebra.TensorProduct.liftEquivRight_apply, Algebra.TensorProduct.lift_tmul]
      rfl
    homEquiv_naturality_right := by
      intro X Y Y' f g
      letI : Algebra R (Y : Type) :=
        ((algebraMap T (Y : Type)).comp (algebraMap R T)).toAlgebra
      letI : IsScalarTower R T (Y : Type) := IsScalarTower.of_algebraMap_eq' rfl
      letI : Algebra R (Y' : Type) :=
        ((algebraMap T (Y' : Type)).comp (algebraMap R T)).toAlgebra
      letI : IsScalarTower R T (Y' : Type) := IsScalarTower.of_algebraMap_eq' rfl
      change CommAlgCat.ofHom ((Algebra.TensorProduct.liftEquivRight (R := R) (S := T)
          (B := (X : Type)) (C := (Y' : Type))).symm (CommAlgCat.Hom.hom (f ≫ g)))
        = CommAlgCat.ofHom ((Algebra.TensorProduct.liftEquivRight (R := R) (S := T)
            (B := (X : Type)) (C := (Y : Type))).symm (CommAlgCat.Hom.hom f)) ≫
          restrictScalars.map g
      apply CommAlgCat.hom_ext
      ext x
      simp [restrictScalars, CommAlgCat.hom_comp, AlgHom.comp_apply,
        Algebra.TensorProduct.liftEquivRight_symm_apply, Algebra.TensorProduct.includeRight_apply]
  }

/-- extendScalars is a left adjoint, hence it preserves all colimits. -/
instance extendScalars_isLeftAdjoint : (extendScalars (R := R) (T := T)).IsLeftAdjoint := ⟨_, ⟨adj⟩⟩

end ChangeOfRings

/-! ### 2. Transfer of colimit preservation through full subcategories -/

/-- If an ambient functor G : C ⥤ D preserves J-colimits, and the full subcategories
P.FullSubcategory, P'.FullSubcategory create J-colimits, then a functor
F : P.FullSubcategory ⥤ P'.FullSubcategory with P.ι ⋙ G = F ⋙ P'.ι also preserves
J-colimits.

The proof reflects the P'.ι-image of the cocone, rewrites it as the G-image of the
P.ι-image, and uses that both P.ι and G preserve the relevant colimits. -/
lemma preservesColimitsOfShape_of_restrict
    {C D : Type*} [Category C] [Category D]
    {P : ObjectProperty C} {P' : ObjectProperty D}
    (J : Type*) [Category J]
    (G : C ⥤ D) (F : P.FullSubcategory ⥤ P'.FullSubcategory)
    (hFG : P.ι ⋙ G = F ⋙ P'.ι)
    [P.IsClosedUnderColimitsOfShape J] [P'.IsClosedUnderColimitsOfShape J]
    [HasColimitsOfShape J C] [HasColimitsOfShape J D]
    [PreservesColimitsOfShape J G] : PreservesColimitsOfShape J F where
  preservesColimit {K} := by
    refine preservesColimit_of_preserves_colimit_cocone (colimit.isColimit K) ?_
    apply isColimitOfReflects P'.ι
    have h1 : IsColimit (G.mapCocone (P.ι.mapCocone (colimit.cocone K))) :=
      isColimitOfPreserves G (isColimitOfPreserves P.ι (colimit.isColimit K))
    have h2 : IsColimit ((P.ι ⋙ G).mapCocone (colimit.cocone K)) :=
      IsColimit.ofIsoColimit h1
        (Functor.mapCoconeMapCocone (H := P.ι) (H' := G) (c := colimit.cocone K)).symm
    rw [hFG] at h2
    exact IsColimit.ofIsoColimit h2
      (Functor.mapCoconeMapCocone (H := F) (H' := P'.ι) (c := colimit.cocone K))

/-! ### 3. Base change preserves pushouts -/

section BaseChange

variable {R : Type} [CommRing R] {T : Type} [CommRing T] [Algebra R T]

/-- The base change functor bc K is the restriction of the ambient extension of scalars. -/
lemma bc_eq_restrict_extendScalars :
    (CommAlgCat.finiteEtale R).ι ⋙ (extendScalars (R := R) (T := T)) =
      (CommAlgCat.FiniteEtale.baseChange.{0} R T) ⋙ (CommAlgCat.finiteEtale T).ι := rfl

/-- **Base change preserves pushouts.** The concrete coherence is hidden in the adjunction
extendScalars -| restrictScalars: extension of scalars is a left adjoint, hence preserves
colimits, and S1745's closure of finite etale algebras under pushouts lets us descend to
the full subcategories. -/
theorem bc_preservesColimitsOfShape_walkingSpan :
    PreservesColimitsOfShape WalkingSpan (CommAlgCat.FiniteEtale.baseChange.{0} R T) :=
  preservesColimitsOfShape_of_restrict WalkingSpan (extendScalars (R := R) (T := T)) (CommAlgCat.FiniteEtale.baseChange.{0} R T)
    (bc_eq_restrict_extendScalars (R := R) (T := T))

/-- **Base change along an arbitrary ring map preserves pullbacks in the opposite
category** (equivalently: base change preserves pushouts). -/
theorem bc_op_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (CommAlgCat.FiniteEtale.baseChange.{0} R T).op := by
  haveI : PreservesColimitsOfShape WalkingSpan (CommAlgCat.FiniteEtale.baseChange.{0} R T) :=
    bc_preservesColimitsOfShape_walkingSpan
  haveI : PreservesColimitsOfShape (WalkingCospanᵒᵖ) (CommAlgCat.FiniteEtale.baseChange.{0} R T) :=
    preservesColimitsOfShape_of_equiv walkingCospanOpEquiv.symm (CommAlgCat.FiniteEtale.baseChange.{0} R T)
  exact preservesLimitsOfShape_op WalkingCospan (CommAlgCat.FiniteEtale.baseChange.{0} R T)

end BaseChange


end S1835Adj

/-- Base change along `R' -> Omega` preserves pushouts of finite etale algebras, hence its
opposite preserves pullbacks. -/
theorem S1835BCPreservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (S1835BC).op :=
  S1835Adj.bc_op_preservesPullbacks (R := S1779R) (T := S1835Omega)

/-- **Field 2** of `PreGaloisCategory.FiberFunctor`: the geometric fibre functor at
(0,0)/AlgebraicClosure F' preserves pullbacks.  It is reduced to the base-change coherence
and discharged by the adjunction above. -/
theorem S1835PreservesPullbacks [PreGaloisCategory S1779AlgR] :
    PreservesLimitsOfShape WalkingCospan (S1835Fiber) := by
  haveI : PreservesLimitsOfShape WalkingCospan (S1835BC).op := S1835BCPreservesPullbacks
  haveI : PreservesLimitsOfShape WalkingCospan (S1835E) := inferInstance
  haveI : PreservesLimitsOfShape WalkingCospan ((S1835BC).op ⋙ S1835E) := inferInstance
  exact preservesLimitsOfShape_of_natIso (S1835FiberIso).symm


/-! ## Field 3: finite coproducts (finite products of algebras)

The same product computation as S1807 (which was stated for a field `K`), now over the
coordinate ring `R'`: tensor product with `Omega` commutes with finite products of
algebras, unconditionally. -/

namespace S1835Pi

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

variable {R : Type} [CommRing R] {T : Type} [CommRing T] [Algebra R T]

lemma piRight_comp_eval {J : Type} [Fintype J] [DecidableEq J]
    (A : J → CommAlgCat.FiniteEtale.{0} R) (j : J) :
    (Algebra.TensorProduct.map (AlgHom.id T T)
        (Pi.evalAlgHom R (fun i => (A i : Type)) j) :
      T ⊗[R] (∀ i, (A i : Type)) →ₐ[T] T ⊗[R] (A j : Type))
      = (Pi.evalAlgHom T (fun i => T ⊗[R] (A i : Type)) j).comp
          (Algebra.TensorProduct.piRight R T T (fun i => (A i : Type))).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro a f
  simp [Algebra.TensorProduct.piRight_tmul]

noncomputable def bc_piFan_isLimit {J : Type} [Fintype J]
    (A : J → CommAlgCat.FiniteEtale.{0} R) :
    IsLimit ((CommAlgCat.FiniteEtale.baseChange.{0} R T).mapCone (piFan R J A)) := by
  classical
  have key : IsLimit (Fan.mk ((CommAlgCat.FiniteEtale.baseChange.{0} R T).obj (piFan R J A).pt)
      (fun j => (CommAlgCat.FiniteEtale.baseChange.{0} R T).map ((piFan R J A).proj j))) := by
    have e : (Fan.mk ((CommAlgCat.FiniteEtale.baseChange.{0} R T).obj (piFan R J A).pt)
        (fun j => (CommAlgCat.FiniteEtale.baseChange.{0} R T).map ((piFan R J A).proj j))) ≅
        piFan T J (fun j => (CommAlgCat.FiniteEtale.baseChange.{0} R T).obj (A j)) := by
      refine Fan.ext (CommAlgCat.FiniteEtale.isoMk (Algebra.TensorProduct.piRight R T T (fun j => (A j : Type)))) ?_
      intro j
      apply ObjectProperty.hom_ext
      apply CommAlgCat.hom_ext
      exact piRight_comp_eval A j
    exact IsLimit.ofIsoLimit (piFanIsLimit T J (fun j => (CommAlgCat.FiniteEtale.baseChange.{0} R T).obj (A j))) e.symm
  exact (isLimitMapConeFanMkEquiv (CommAlgCat.FiniteEtale.baseChange.{0} R T) A (fun j => (piFan R J A).proj j)).invFun key

instance bc_preservesFiniteProducts :
    PreservesFiniteProducts (CommAlgCat.FiniteEtale.baseChange.{0} R T) where
  preserves n := by
    haveI : ∀ (f : Fin n → CommAlgCat.FiniteEtale.{0} R),
        PreservesLimit (Discrete.functor f) (CommAlgCat.FiniteEtale.baseChange.{0} R T) :=
      fun f => preservesLimit_of_preserves_limit_cone (piFanIsLimit R (Fin n) f)
        (bc_piFan_isLimit f)
    exact preservesLimitsOfShape_of_discrete (CommAlgCat.FiniteEtale.baseChange.{0} R T)

end PiBC


end S1835Pi

/-- Base change along `R' -> Omega` preserves finite products of finite etale algebras. -/
theorem S1835BCPreservesFiniteProducts : PreservesFiniteProducts S1835BC :=
  S1835Pi.bc_preservesFiniteProducts (R := S1779R) (T := S1835Omega)

/-- **Field 3** of `PreGaloisCategory.FiberFunctor`: the geometric fibre functor at
(0,0)/AlgebraicClosure F' preserves finite coproducts. -/
theorem S1835PreservesFiniteCoproducts [PreGaloisCategory S1779AlgR] :
    PreservesFiniteCoproducts (S1835Fiber) where
  preserves n := by
    haveI : PreservesFiniteProducts S1835BC := S1835BCPreservesFiniteProducts
    haveI : PreservesFiniteCoproducts (S1835BC).op := preservesFiniteCoproducts_op S1835BC
    haveI : PreservesFiniteCoproducts (S1835E) := inferInstance
    haveI : PreservesFiniteCoproducts ((S1835BC).op ⋙ S1835E) := inferInstance
    exact preservesColimitsOfShape_of_natIso (S1835FiberIso).symm


/-! ## Fields 4--6: the exact base-change conditions

For the remaining three fields the reduction is formal (S1769): the fibre functor is
isomorphic to `(bc).op >>> fiber Omega Omega`, and `fiber Omega Omega` is an equivalence
(`CommAlgCat.FiniteEtale.equivOfIsSepClosed`), so every preservation/reflection property of
the composite follows from the same property of `(bc).op`.  The three conditions below are
therefore the *exact* remaining inputs, stated for the actual base change functor
`R' -> Omega` and not weakened. -/

/-- The base-change condition for field 4: the opposite of base change preserves
epimorphisms, i.e. base change preserves monomorphisms of finite etale R'-algebras. -/
def S1835BCPreservesEpis : Prop := Functor.PreservesEpimorphisms (S1835BC).op

/-- The base-change condition for field 5: base change preserves limits over the finite
one-object groupoid of a finite group (equivalently, fixed points commute with the base
change `R' -> Omega`). -/
def S1835BCPreservesQuotients : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PreservesColimitsOfShape (SingleObj G) (S1835BC).op

/-- The base-change condition for field 6: the opposite of base change along
`R' -> Omega` reflects isomorphisms of finite etale algebras (equivalently, base change
itself reflects isomorphisms). -/
def S1835BCReflectsIsos : Prop := (S1835BC).op.ReflectsIsomorphisms

/-- **Field 4**, from the exact base-change condition. -/
theorem S1835PreservesEpis_of (h : S1835BCPreservesEpis) :
    Functor.PreservesEpimorphisms (S1835Fiber) := by
  haveI : Functor.PreservesEpimorphisms (S1835BC).op := h
  haveI : Functor.PreservesEpimorphisms (S1835E) := inferInstance
  haveI : Functor.PreservesEpimorphisms ((S1835BC).op ⋙ S1835E) := inferInstance
  exact Functor.preservesEpimorphisms.of_iso (S1835FiberIso).symm

/-- **Field 5**, from the exact base-change condition. -/
theorem S1835PreservesQuotients_of (h : S1835BCPreservesQuotients) :
    ∀ (G : Type) [Group G] [Finite G], PreservesColimitsOfShape (SingleObj G) (S1835Fiber) := by
  intro G _ _
  haveI := h G
  haveI : PreservesColimitsOfShape (SingleObj G) (S1835E) := inferInstance
  haveI : PreservesColimitsOfShape (SingleObj G) ((S1835BC).op ⋙ S1835E) := inferInstance
  exact preservesColimitsOfShape_of_natIso (S1835FiberIso).symm

/-- **Field 6**, from the exact base-change condition. -/
theorem S1835ReflectsIsos_of (h : S1835BCReflectsIsos) :
    (S1835Fiber).ReflectsIsomorphisms := by
  haveI : (S1835BC).op.ReflectsIsomorphisms := h
  haveI : ((S1835BC).op ⋙ S1835E).ReflectsIsomorphisms := inferInstance
  exact reflectsIsomorphisms_of_iso (S1835FiberIso).symm


/-! ## The concrete content of the first missing field

Field 4 (`preservesEpis`) reduces to `S1835BCPreservesEpis`, i.e. to the statement that the
base change functor `R' -> Omega` preserves monomorphisms of finite etale algebras.  The
theorem below identifies a concrete, element-level sufficient form of that statement: for
every monomorphism `f : X ⟶ Y` of finite etale `R'`-algebras, the induced `Omega`-linear
map `Omega (x)_{R'} X -> Omega (x)_{R'} Y` is injective.  This is exactly the algebraic
content that has to be added; it is not a weakening (it implies field 4 verbatim). -/

/-- Injectivity of the underlying algebra map gives a monomorphism in the category of finite
etale algebras over a commutative ring. -/
theorem S1835InjectiveMono {R : Type} [CommRing R]
    {X Y : CommAlgCat.FiniteEtale.{0} R} (f : X ⟶ Y)
    (hf : Function.Injective (fun x : (X : Type) => f.hom.hom x)) : Mono f := by
  refine ⟨fun {Z} g h hgh => ?_⟩
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro z
  apply hf
  have h := congrArg
    (fun (m : Z ⟶ Y) => (m.hom.hom) z) hgh
  simpa [CommAlgCat.hom_comp, AlgHom.comp_apply] using h

/-- **The concrete content of the first missing field.**  Base change along `R' -> Omega`
is injective on monomorphisms of finite etale `R'`-algebras: for every mono `f : X ⟶ Y`,
the induced map `Omega (x)_{R'} X -> Omega (x)_{R'} Y` is injective. -/
def S1835BCInjectiveOnMonos : Prop :=
  ∀ {X Y : CommAlgCat.FiniteEtale.{0} S1779R} (f : X ⟶ Y), Mono f →
    Function.Injective (fun x : S1835Omega ⊗[S1779R] (X : Type) =>
      Algebra.TensorProduct.map (AlgHom.id S1835Omega S1835Omega) f.hom.hom x)

/-- **The concrete statement implies field 4 verbatim.** -/
theorem S1835BCPreservesEpis_of_injectiveOnMonos (h : S1835BCInjectiveOnMonos) :
    S1835BCPreservesEpis := by
  haveI hmono : Functor.PreservesMonomorphisms S1835BC :=
    ⟨fun {X Y} f hf => S1835InjectiveMono (S1835BC.map f) (h f hf)⟩
  refine ⟨fun {X Y} f hf => ?_⟩
  rw [Functor.op_map]
  exact (op_epi_iff ((S1835BC).map f.unop)).mpr inferInstance

/-- **The concrete content of field 6.**  Base change along `R' -> Omega` reflects
isomorphisms, in element-free form: if `f` becomes an isomorphism after base change, then
`f` is an isomorphism. -/
def S1835BCReflectsIsosConcrete : Prop :=
  ∀ {X Y : (CommAlgCat.FiniteEtale.{0} S1779R)ᵒᵖ} (f : X ⟶ Y),
    IsIso ((S1835BC).op.map f) → IsIso f

/-- Field 6 is exactly its concrete form. -/
theorem S1835BCReflectsIsos_iff_concrete :
    S1835BCReflectsIsos ↔ S1835BCReflectsIsosConcrete := by
  constructor
  · intro h X Y f hf
    haveI : (S1835BC).op.ReflectsIsomorphisms := h
    haveI : IsIso ((S1835BC).op.map f) := hf
    exact Functor.ReflectsIsomorphisms.reflects (S1835BC).op f
  · intro h
    exact ⟨fun {X Y} f hf => h f hf⟩

/-- **The exact first missing input**, in the order of the six class fields: field 4. -/
def S1835FirstMissing : Prop := S1835BCPreservesEpis

/-- The complete exact remaining content for the six-field `FiberFunctor`: fields 4, 5, 6. -/
def S1835SixFieldsMissing : Prop :=
  S1835BCPreservesEpis ∧ S1835BCPreservesQuotients ∧ S1835BCReflectsIsos

/-- The six-field assembly: the unconditional fields 1--3 and the three reduced ones. -/
@[implicit_reducible]
noncomputable def S1835FiberFunctorOf (hEpi : S1835BCPreservesEpis)
    (hQuot : S1835BCPreservesQuotients) (hIso : S1835BCReflectsIsos)
    [PreGaloisCategory S1779AlgR] :
    @PreGaloisCategory.FiberFunctor S1779AlgR S1779AlgR_category
      ‹PreGaloisCategory S1779AlgR› S1835Fiber where
  preservesTerminalObjects := S1835PreservesTerminalObjects
  preservesPullbacks := S1835PreservesPullbacks
  preservesFiniteCoproducts := S1835PreservesFiniteCoproducts
  preservesEpis := S1835PreservesEpis_of hEpi
  preservesQuotientsByFiniteGroups := S1835PreservesQuotients_of hQuot
  reflectsIsos := S1835ReflectsIsos_of hIso

/-- **The six fields from exactly the remaining content.**  Fields 1--3 are unconditional
(`S1835PreservesTerminalObjects`, `S1835PreservesPullbacks`,
`S1835PreservesFiniteCoproducts`); fields 4--6 are exactly `S1835SixFieldsMissing`. -/
theorem S1835FiberFunctor_of_missing (h : S1835SixFieldsMissing)
    [PreGaloisCategory S1779AlgR] :
    PreGaloisCategory.FiberFunctor S1835Fiber :=
  S1835FiberFunctorOf h.1 h.2.1 h.2.2

#check S1835FiberIso
#check S1835EEquiv
#check S1830Main.S1830PreGaloisCategory
#check S1835PreservesTerminalObjects
#check S1835BCPreservesPullbacks
#check S1835PreservesPullbacks
#check S1835BCPreservesFiniteProducts
#check S1835PreservesFiniteCoproducts
#check S1835BCPreservesEpis
#check S1835PreservesEpis_of
#check S1835PreservesQuotients_of
#check S1835ReflectsIsos_of
#check S1835InjectiveMono
#check S1835BCInjectiveOnMonos
#check S1835BCPreservesEpis_of_injectiveOnMonos
#check S1835BCReflectsIsosConcrete
#check S1835BCReflectsIsos_iff_concrete
#check S1835FiberFunctorOf
#check S1835FirstMissing
#check S1835SixFieldsMissing
#check S1835FiberFunctor_of_missing

/-! ## Axiom audit -/

#print axioms S1835FiberIso
#print axioms S1835PreservesTerminalObjects
#print axioms S1835BCPreservesPullbacks
#print axioms S1835PreservesPullbacks
#print axioms S1835BCPreservesFiniteProducts
#print axioms S1835PreservesFiniteCoproducts
#print axioms S1835PreservesEpis_of
#print axioms S1835PreservesQuotients_of
#print axioms S1835ReflectsIsos_of
#print axioms S1835InjectiveMono
#print axioms S1835BCPreservesEpis_of_injectiveOnMonos
#print axioms S1835BCReflectsIsos_iff_concrete
#print axioms S1835FiberFunctorOf
#print axioms S1835FiberFunctor_of_missing

end LeanFormal.IUT.XiFPaper.S1835FiberRPrimeActual