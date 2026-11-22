/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF / S1769

# S1769 -- the six fields of `PreGaloisCategory.FiberFunctor (geometricFiber K)`

Task: construct, field by field, the six fields of

  `PreGaloisCategory.FiberFunctor (CommAlgCat.FiniteEtale.fiber K (AlgebraicClosure K))`

for a field `K`, or report the precise first missing piece.  This file reports both:

* **field 1** (`preservesTerminalObjects`) is proved unconditionally, modulo the ambient
  `[PreGaloisCategory (FiniteEtale K)^op]` instance;
* **field 6** (`reflectsIsos`) is proved unconditionally, modulo the same ambient instance;
* **fields 2, 3, 4, 5** are reduced, without changing any statement, to four exact properties
  of Mathlib's `CommAlgCat.FiniteEtale.baseChange K (AlgebraicClosure K)`:

  * `BCPreservesPullbacks`: `PreservesLimitsOfShape WalkingCospan (baseChange K Kbar).op`,
  * `BCPreservesFiniteProducts`: `PreservesFiniteProducts (baseChange K Kbar)`,
  * `BCPreservesEpis`: `PreservesEpimorphisms (baseChange K Kbar).op`,
  * `BCPreservesQuotients`: `forall G [Group G] [Finite G],
       PreservesColimitsOfShape (SingleObj G) (baseChange K Kbar).op`.

The reduction uses the Mathlib isomorphism
`CommAlgCat.FiniteEtale.fiberIsoBaseChangeFiber`

  `fiber K Kbar ~= (baseChange K Kbar).op >>> fiber Kbar Kbar`,

and the fact proved in Mathlib (`CommAlgCat.FiniteEtale.equivOfIsSepClosed`) that the
second factor is an equivalence of categories.  Consequently every preservation property
of the composite follows from the same property of the first factor.

## Exact first missing

The first missing field in the order of the task is **field 2, `preservesPullbacks`**.
Its exact remaining input is `BCPreservesPullbacks K`, i.e. the functor
`CommAlgCat.FiniteEtale.baseChange K Kbar` preserves pushouts (equivalently, its opposite
preserves pullbacks).  Mathlib has the corresponding **ambient** statements in
`Mathlib/Algebra/Category/Ring/Under/Limits.lean`:
`CommRingCat.Under.tensorProd` preserves finite limits when the base extension is flat
(`CommRingCat.Under.tensorProd` is `Under.pushout` up to natural isomorphism, and
`Under.pushout` is a left adjoint), and `Under.pushout` preserves colimits.  What is not
in Mathlib is the transfer of these statements through the full subcategories
`CommAlgCat.FiniteEtale K` and `CommAlgCat.FiniteEtale Kbar`, i.e. the restriction of the
ambient base-change functor to finite etale algebras and the identification of its finite
(co)limits with those of the ambient category.

## What is *not* done

No `sorry`, no `admit`, no new axiom and no weakened statement occurs in this file.  The
four remaining conditions are explicit hypotheses of the final `fiberFunctorOf`.
-/
import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.FieldTheory.AbsoluteGaloisGroup

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace S1769

/-! ### 0. The category, the geometric fibre and base change -/

/-- The opposite of the category of finite etale `K`-algebras: the Galois category of
affine finite etale `K`-schemes. -/
abbrev C (K : Type) [Field K] : Type 1 := (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ

/-- The geometric fibre functor `S |-> Hom_K(S, Kbar)`.  This is exactly Mathlib's
`CommAlgCat.FiniteEtale.fiber K (AlgebraicClosure K)`. -/
abbrev F (K : Type) [Field K] : C K ⥤ FintypeCat.{0} :=
  CommAlgCat.FiniteEtale.fiber K (AlgebraicClosure K)

/-- Mathlib's base change functor `A |-> Kbar (x)_K A` on finite etale algebras. -/
abbrev bc (K : Type) [Field K] :
    CommAlgCat.FiniteEtale.{0} K ⥤ CommAlgCat.FiniteEtale.{0} (AlgebraicClosure K) :=
  CommAlgCat.FiniteEtale.baseChange K (AlgebraicClosure K)

/-- The fibre functor over the separably closed field `Kbar = AlgebraicClosure K`.  It is an
equivalence by `CommAlgCat.FiniteEtale.equivOfIsSepClosed`. -/
abbrev E (K : Type) [Field K] :
    (CommAlgCat.FiniteEtale.{0} (AlgebraicClosure K))ᵒᵖ ⥤ FintypeCat.{0} :=
  CommAlgCat.FiniteEtale.fiber (AlgebraicClosure K) (AlgebraicClosure K)

/-- Mathlib's comparison `fiber K Kbar ~= (baseChange K Kbar).op >>> fiber Kbar Kbar`. -/
def fiberIso (K : Type) [Field K] : F K ≅ (bc K).op ⋙ E K :=
  CommAlgCat.FiniteEtale.fiberIsoBaseChangeFiber
    (R := K) (Ω := AlgebraicClosure K) (S := AlgebraicClosure K)

/-! ### 1. The terminal object and the first field

The terminal object of `(FiniteEtale K)^op` is `op K`.  Its fibre is `Hom_K(K, Kbar)`, a
one-point type.  The proof below is the categorical packaging of this computation.
-/

/-- `K` is initial in `FiniteEtale K`: every finite etale `K`-algebra receives a unique
`K`-algebra map from `K`. -/
instance selfInitial (K : Type) [Field K] (X : CommAlgCat.FiniteEtale.{0} K) :
    Unique (CommAlgCat.FiniteEtale.of K K ⟶ X) where
  default := CommAlgCat.FiniteEtale.ofHom (Algebra.ofId K X.obj)
  uniq f := by
    apply InducedCategory.hom_ext
    ext

def selfInitialObj (K : Type) [Field K] : IsInitial (CommAlgCat.FiniteEtale.of K K) :=
  IsInitial.ofUnique _

def selfTerminal (K : Type) [Field K] :
    IsTerminal (Opposite.op (CommAlgCat.FiniteEtale.of K K)) :=
  (selfInitialObj K).op

def terminalIsoSelf (K : Type) [Field K] [PreGaloisCategory (C K)] :
    (⊤_ (C K)) ≅ Opposite.op (CommAlgCat.FiniteEtale.of K K) :=
  terminalIsTerminal.uniqueUpToIso (selfTerminal K)

theorem terminal_obj_subsingleton (K : Type) [Field K] [PreGaloisCategory (C K)] :
    Subsingleton ((F K).obj (⊤_ (C K)) : Type) := by
  let e := (F K).mapIso (terminalIsoSelf K)
  let ee : ((F K).obj (⊤_ (C K)) : Type) ≃
      ((F K).obj (Opposite.op (CommAlgCat.FiniteEtale.of K K)) : Type) :=
    FintypeCat.equivEquivIso.symm e
  haveI : Subsingleton ((F K).obj (Opposite.op (CommAlgCat.FiniteEtale.of K K)) : Type) := by
    change Subsingleton ((CommAlgCat.FiniteEtale.of K K).obj →ₐ[K] AlgebraicClosure K)
    infer_instance
  refine ⟨fun x y => ?_⟩
  apply ee.injective
  exact Subsingleton.elim _ _

theorem terminal_obj_nonempty (K : Type) [Field K] [PreGaloisCategory (C K)] :
    Nonempty ((F K).obj (⊤_ (C K)) : Type) := by
  let e := (F K).mapIso (terminalIsoSelf K)
  let ee : ((F K).obj (⊤_ (C K)) : Type) ≃
      ((F K).obj (Opposite.op (CommAlgCat.FiniteEtale.of K K)) : Type) :=
    FintypeCat.equivEquivIso.symm e
  exact ⟨ee.symm (Algebra.ofId K (AlgebraicClosure K))⟩

def terminal_obj_isTerminal (K : Type) [Field K] [PreGaloisCategory (C K)] :
    IsTerminal ((F K).obj (⊤_ (C K))) := by
  haveI : Subsingleton ((F K).obj (⊤_ (C K)) : Type) := terminal_obj_subsingleton K
  haveI : Nonempty ((F K).obj (⊤_ (C K)) : Type) := terminal_obj_nonempty K
  refine IsTerminal.ofUniqueHom (fun Y => FintypeCat.homMk (fun _ => Classical.arbitrary _)) ?_
  intro Y m
  apply FintypeCat.hom_ext
  intro y
  exact Subsingleton.elim _ _

/-- **Field 1** of `PreGaloisCategory.FiberFunctor`: `F` preserves terminal objects. -/
theorem preservesTerminalObjects (K : Type) [Field K] [PreGaloisCategory (C K)] :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (F K) := by
  have h : PreservesLimit (Functor.empty.{0} (C K)) (F K) := by
    let e : (F K).obj (⊤_ (C K)) ≅ ⊤_ FintypeCat :=
      (terminal_obj_isTerminal K).uniqueUpToIso terminalIsTerminal
    exact preservesTerminal_of_iso (F K) e
  haveI := h
  exact preservesLimitsOfShape_pempty_of_preservesTerminal (G := F K)

/-! ### 2. Base change reflects isomorphisms (field 6)

`bc K : FiniteEtale K ⥤ FiniteEtale Kbar` is `Kbar (x)_K -`.  Since `Kbar` is a free
`K`-module (in particular faithfully flat), it is conservative: if `Kbar (x)_K f` is an
isomorphism, so is `f`.  The proof uses Mathlib's
`Module.FaithfullyFlat.lTensor_bijective_iff_bijective`.
-/

instance bc_reflectsIsos (K : Type) [Field K] : (bc K).ReflectsIsomorphisms where
  reflects {A B} f hf := by
    haveI : IsIso ((bc K).map f).hom :=
      (ObjectProperty.isIso_hom_iff ((bc K).map f)).mpr hf
    have hbij : Function.Bijective (((bc K).map f).hom.hom) := by
      exact (ConcreteCategory.isIso_iff_bijective ((bc K).map f).hom).mp inferInstance
    have hbij' : Function.Bijective (fun x : (AlgebraicClosure K) ⊗[K] (A.obj : Type) =>
        (LinearMap.lTensor (AlgebraicClosure K) f.hom.hom.toLinearMap) x) := by
      change Function.Bijective (fun x : (AlgebraicClosure K) ⊗[K] (A.obj : Type) =>
          (((bc K).map f).hom.hom) x) at hbij
      exact hbij
    have hf' : Function.Bijective f.hom.hom.toLinearMap := by
      exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective (R := K)
        (M := AlgebraicClosure K) (f := f.hom.hom.toLinearMap)).mp hbij'
    have hf'' : Function.Bijective f.hom.hom := hf'
    haveI : IsIso f.hom := (ConcreteCategory.isIso_iff_bijective f.hom).mpr hf''
    exact (ObjectProperty.isIso_hom_iff f).mp inferInstance

instance bc_op_reflectsIsos (K : Type) [Field K] : (bc K).op.ReflectsIsomorphisms where
  reflects {X Y} f hf := by
    haveI : IsIso ((bc K).map f.unop) := by
      rw [Functor.op_map] at hf
      exact (isIso_op_iff ((bc K).map f.unop)).mp hf
    have h2 : IsIso f.unop := isIso_of_reflects_iso f.unop (bc K)
    exact (isIso_unop_iff f).mp h2

/-- **Field 6** of `PreGaloisCategory.FiberFunctor`: `F` reflects isomorphisms. -/
theorem reflectsIsos (K : Type) [Field K] [PreGaloisCategory (C K)] :
    (F K).ReflectsIsomorphisms := by
  haveI : ((bc K).op ⋙ E K).ReflectsIsomorphisms := inferInstance
  exact reflectsIsomorphisms_of_iso (fiberIso K).symm

/-! ### 3. The four exact base-change conditions

These are the *only* remaining inputs.  They are stated for Mathlib's
`CommAlgCat.FiniteEtale.baseChange K Kbar`, not for the fibre functor, and are not
weakened or changed.
-/

/-- **Condition for field 2.**  Base change preserves pushouts, equivalently its opposite
preserves pullbacks. -/
def BCPreservesPullbacks (K : Type) [Field K] : Prop :=
  PreservesLimitsOfShape WalkingCospan (bc K).op

/-- **Condition for field 3.**  Base change preserves finite products. -/
def BCPreservesFiniteProducts (K : Type) [Field K] : Prop :=
  PreservesFiniteProducts (bc K)

/-- **Condition for field 4.**  The opposite of base change preserves epimorphisms
(equivalently, base change preserves monomorphisms). -/
def BCPreservesEpis (K : Type) [Field K] : Prop :=
  Functor.PreservesEpimorphisms (bc K).op

/-- **Condition for field 5.**  Base change preserves limits over the finite one-object
groupoid of a finite group `G`; in the opposite category this is preservation of quotients
by finite groups. -/
def BCPreservesQuotients (K : Type) [Field K] : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PreservesColimitsOfShape (SingleObj G) (bc K).op

/-! ### 4. Reductions of the four fields to the base-change conditions -/

theorem preservesPullbacks_of (K : Type) [Field K] [PreGaloisCategory (C K)]
    (h : BCPreservesPullbacks K) :
    PreservesLimitsOfShape WalkingCospan (F K) := by
  haveI : PreservesLimitsOfShape WalkingCospan (bc K).op := h
  haveI : PreservesLimitsOfShape WalkingCospan (E K) := inferInstance
  haveI : PreservesLimitsOfShape WalkingCospan ((bc K).op ⋙ E K) := inferInstance
  exact preservesLimitsOfShape_of_natIso (fiberIso K).symm

theorem preservesFiniteCoproducts_of (K : Type) [Field K] [PreGaloisCategory (C K)]
    (h : BCPreservesFiniteProducts K) :
    PreservesFiniteCoproducts (F K) where
  preserves n := by
    haveI : PreservesFiniteProducts (bc K) := h
    haveI : PreservesFiniteCoproducts (bc K).op := preservesFiniteCoproducts_op (bc K)
    haveI : PreservesFiniteCoproducts (E K) := inferInstance
    haveI : PreservesFiniteCoproducts ((bc K).op ⋙ E K) := inferInstance
    exact preservesColimitsOfShape_of_natIso (fiberIso K).symm

theorem preservesEpis_of (K : Type) [Field K] [PreGaloisCategory (C K)]
    (h : BCPreservesEpis K) :
    Functor.PreservesEpimorphisms (F K) := by
  haveI : Functor.PreservesEpimorphisms (bc K).op := h
  haveI : Functor.PreservesEpimorphisms ((bc K).op ⋙ E K) := inferInstance
  exact Functor.preservesEpimorphisms.of_iso (fiberIso K).symm

theorem preservesQuotients_of (K : Type) [Field K] [PreGaloisCategory (C K)]
    (h : BCPreservesQuotients K) :
    ∀ (G : Type) [Group G] [Finite G], PreservesColimitsOfShape (SingleObj G) (F K) := by
  intro G _ _
  haveI := h G
  haveI : PreservesColimitsOfShape (SingleObj G) (E K) := inferInstance
  haveI : PreservesColimitsOfShape (SingleObj G) ((bc K).op ⋙ E K) := inferInstance
  exact preservesColimitsOfShape_of_natIso (fiberIso K).symm

/-! ### 5. Conditional assembly of the fibre functor -/

set_option linter.defProp false in
/-- The fibre functor `F K`, assuming the four exact base-change conditions above.
Fields 1 and 6 are proved unconditionally; fields 2--5 are the reductions of Section 4. -/
@[implicit_reducible]
def fiberFunctorOf (K : Type) [Field K] [PreGaloisCategory (C K)]
    (hPull : BCPreservesPullbacks K)
    (hCoprod : BCPreservesFiniteProducts K)
    (hEpi : BCPreservesEpis K)
    (hQuot : BCPreservesQuotients K) :
    PreGaloisCategory.FiberFunctor (F K) where
  preservesTerminalObjects := preservesTerminalObjects K
  preservesPullbacks := preservesPullbacks_of K hPull
  preservesFiniteCoproducts := preservesFiniteCoproducts_of K hCoprod
  preservesEpis := preservesEpis_of K hEpi
  preservesQuotientsByFiniteGroups := preservesQuotients_of K hQuot
  reflectsIsos := reflectsIsos K

/-! ### 6. Field status and the exact first missing -/

/-- The names of the six fields, with `true` exactly for the two fields proved in this file. -/
structure FieldStatus where
  preservesTerminalObjects : Bool
  preservesPullbacks : Bool
  preservesFiniteCoproducts : Bool
  preservesEpis : Bool
  preservesQuotientsByFiniteGroups : Bool
  reflectsIsos : Bool

/-- Status at the end of S1769: fields 1 and 6 are proved; fields 2--5 are reduced to the
four base-change conditions. -/
def fieldStatus : FieldStatus where
  preservesTerminalObjects := true
  preservesPullbacks := false
  preservesFiniteCoproducts := false
  preservesEpis := false
  preservesQuotientsByFiniteGroups := false
  reflectsIsos := true

/-- The exact first missing field, in the order of the six fields. -/
def firstMissing : String := "preservesPullbacks (BCPreservesPullbacks K)"

/-- The exact first missing mathematical input: `CommAlgCat.FiniteEtale.baseChange K Kbar`
preserves pushouts (equivalently, its opposite preserves pullbacks). -/
def FirstMissing (K : Type) [Field K] : Prop := BCPreservesPullbacks K

theorem fieldStatus_length : fieldStatus.preservesPullbacks = false := rfl

/-! ### 7. Axiom audit -/

#print axioms S1769.preservesTerminalObjects
#print axioms S1769.bc_reflectsIsos
#print axioms S1769.bc_op_reflectsIsos
#print axioms S1769.reflectsIsos
#print axioms S1769.fiberFunctorOf

end S1769