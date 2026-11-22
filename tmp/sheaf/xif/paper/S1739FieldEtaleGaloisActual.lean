/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# S1739 -- finite etale K-algebras as a Galois category (warm-up)

Task: for a field `K`, build the small category of finite etale `K`-algebras / finite separable
extensions as a `Category.{0, 1}`, prove `PreGaloisCategory` / `GaloisCategory` (modelled on
`Action FintypeCat (AbsoluteGaloisProfinite K)` when available) and give the equivalence with
finite sets carrying a continuous action of the absolute Galois group, or the exact missing
pieces.

## Answer

Mathlib (v4.32.2, commit 905b9581) already provides

* `CommAlgCat.FiniteEtale K`, the category of finite etale `K`-algebras
  (`Mathlib/RingTheory/Etale/Finite.lean`, C. Merten, 2026); with `v = 0` it is an honest
  `Category.{0,1}` -- objects live in `Type 1`, hom types in `Type 0`;
* the geometric fibre functor `CommAlgCat.FiniteEtale.fiber K Omega`, `S |-> Hom_K(S, Omega)`, as
  a functor `(FiniteEtale K)^op --> FintypeCat`;
* the abstract Galois category theory: `PreGaloisCategory`, `PreGaloisCategory.FiberFunctor`,
  `GaloisCategory`, and the main theorem that a fibre functor induces an equivalence
  `PreGaloisCategory.functorToContAction F : C ~= ContAction FintypeCat (Aut F)`
  (`Mathlib/CategoryTheory/Galois/Equivalence.lean`);
* `Field.absoluteGaloisGroup K = (AlgebraicClosure K ~=+[K] AlgebraicClosure K)` with the Krull
  topology (`Mathlib/FieldTheory/AbsoluteGaloisGroup.lean`).

Mathlib does *not* provide: an `AbsoluteGaloisProfinite K` bundled profinite group; any
`PreGaloisCategory` instance for a category of algebras (the only `GaloisCategory` instances are
for `Action FintypeCat G` with `G` a finite group); the closure instances of the object property
`CommAlgCat.finiteEtale K` needed to transport the (co)limits of `CommAlgCat K` to the full
subcategory of finite etale algebras; and the identification of `Aut` of the geometric fibre
functor with `Gal(Kbar/K)`.

## Contents of this file

* `FiniteEtaleAlg K` := `(CommAlgCat.FiniteEtale.{0} K)^op` with its `Category.{0,1}` instance,
  the terminal object `self` (= `K`) and the proof that it is terminal -- *kernel checked, no
  sorry*;
* the geometric fibre functor `fiber K Omega` and the computation of its value at the terminal
  object -- *kernel checked, no sorry*;
* a *checked* inventory of which (co)limits Mathlib has in `CommAlgCat K` (checked by instance
  search inside the file), which pinpoints the gap; the algebraic closure ingredients
  `finite_pi`, `etale_pi`, `finite_tensorProduct`, `etale_tensorProduct` are proved here --
  kernel checked, no sorry;
* `instPreGaloisCategory`, `instFiberFunctor`, `instGaloisCategory` and the resulting equivalence
  `galoisEquivalence`, reduced to named missing statements, each with a `sorry` and a docstring
  saying exactly what is missing;
* the comparison `Aut (fiber K Kbar) ~=* Gal(Kbar/K)` stated as an unproved target;
* the unconditional separably closed case (Mathlib);
* `#print axioms` for every declaration of interest.

Nothing is fabricated: every `sorry` is a named, mathematically precise statement, and the axiom
audit at the end separates what is kernel closed from what is conditional.
-/
import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Equivalence
import Mathlib.CategoryTheory.Galois.Examples
import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.FieldTheory.AbsoluteGaloisGroup

universe w u

open CategoryTheory CategoryTheory.Limits

open scoped FintypeCatDiscrete TensorProduct

namespace S1739FieldEtaleGalois

variable (K : Type) [Field K]

/-! ### 1. The category -/

/-- The opposite of the category of finite etale `K`-algebras.

This is the Galois category of finite etale `K`-schemes (the affine ones, i.e. `Spec` of finite
etale `K`-algebras).  The opposite is taken so that the geometric fibre functor
`S |-> Hom_K(S, Kbar)` becomes covariant -- `K` is the initial finite etale `K`-algebra, and it
has to be terminal in a Galois category (Lenstra (G1)).

`CommAlgCat.FiniteEtale.{0} K` has objects in `Type 1` and hom types in `Type 0`, hence it is a
`Category.{0, 1}`; this is the `Category.{0,1}` requested by the task. -/
abbrev FiniteEtaleAlg : Type 1 := (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ

namespace FiniteEtaleAlg

instance category : Category.{0, 1} (FiniteEtaleAlg K) := inferInstance

/-- A finite etale `K`-algebra, bundled as an object of the opposite category. -/
abbrev of (A : Type) [CommRing A] [Algebra K A] [Module.Finite K A] [Algebra.Etale K A] :
    FiniteEtaleAlg K :=
  Opposite.op (CommAlgCat.FiniteEtale.of K A)

/-- The base field itself, as a finite etale `K`-algebra: the terminal object. -/
abbrev self : FiniteEtaleAlg K := of K K

variable {K} in
/-- Every `K`-algebra map `K --> A` is the structure map: `K` is initial in `FiniteEtale K`. -/
theorem hom_self_subsingleton (X : FiniteEtaleAlg K) : Subsingleton (X ⟶ self K) where
  allEq f g := by
    have h : f.unop = g.unop := by
      apply InducedCategory.hom_ext
      apply CommAlgCat.hom_ext
      exact Subsingleton.elim _ _
    exact Quiver.Hom.unop_inj h

instance (X : FiniteEtaleAlg K) : Subsingleton (X ⟶ self K) := hom_self_subsingleton X

instance (X : FiniteEtaleAlg K) : Unique (X ⟶ self K) where
  default := (CommAlgCat.FiniteEtale.ofHom (Algebra.ofId K X.unop.obj)).op
  uniq f := Subsingleton.allEq f _

/-- `K` itself is the terminal object of `(FiniteEtale K)^op` (Lenstra (G1)). -/
def isTerminal_self : IsTerminal (self K) := IsTerminal.ofUnique _

instance : HasTerminal (FiniteEtaleAlg K) := hasTerminal_of_unique (self K)

/-! ### 2. The geometric fibre functor -/

/-- The geometric fibre functor `S |-> Hom_K(S, Omega)` for a geometric point `Omega` of `K`.
This is `CommAlgCat.FiniteEtale.fiber` of Mathlib.  For `Omega` separably closed it is an
equivalence `(FiniteEtale K)^op ~= FintypeCat` (`CommAlgCat.FiniteEtale.equivOfIsSepClosed`). -/
noncomputable abbrev fiber (Ω : Type w) [Field Ω] [Algebra K Ω] :
    FiniteEtaleAlg K ⥤ FintypeCat.{w} :=
  CommAlgCat.FiniteEtale.fiber K Ω

/-- The fibre functor at the geometric point given by an algebraic closure. -/
noncomputable abbrev geometricFiber : FiniteEtaleAlg K ⥤ FintypeCat :=
  fiber K (AlgebraicClosure K)

variable {K} in
/-- The fibre of the base field is a one point set: the fibre functor preserves the terminal
object (Lenstra (G4), the easy half). -/
theorem fiber_self_subsingleton (Ω : Type w) [Field Ω] [Algebra K Ω] :
    Subsingleton (↥((fiber K Ω).obj (self K))) := by
  change Subsingleton (K →ₐ[K] Ω)
  infer_instance

/-! ### 3. Inventory: what Mathlib has, and the exact gap -/

/-- CHECKED: `CommAlgCat K` has finite products, hence a terminal object and pullbacks. -/
example : HasFiniteProducts (CommAlgCat.{0} K) := inferInstance
example : HasTerminal (CommAlgCat.{0} K) := inferInstance
example : HasPullbacks (CommAlgCat.{0} K) := inferInstance

/-- CHECKED: `CommAlgCat K` has finite coproducts, in particular pushouts. -/
example : HasFiniteCoproducts (CommAlgCat.{0} K) := inferInstance
example : HasPushouts (CommAlgCat.{0} K) := inferInstance

/-! #### 3a. The algebraic ingredients, kernel checked

The closure of finite etale algebras under the relevant constructions is available, only not
packaged as `ObjectProperty.IsClosedUnderLimitsOfShape` / `IsClosedUnderColimitsOfShape`.
-/

variable {K} in
/-- CHECKED: a finite product of finite etale `K`-algebras is finite. -/
theorem finite_pi (J : Type) [Fintype J] (A : J → Type) [∀ j, CommRing (A j)]
    [∀ j, Algebra K (A j)] [∀ j, Module.Finite K (A j)] : Module.Finite K (∀ j, A j) :=
  inferInstance

variable {K} in
/-- CHECKED: a finite product of finite etale `K`-algebras is etale
(`Algebra.FormallyEtale.pi_iff`, `Mathlib/RingTheory/Etale/Pi.lean`). -/
theorem etale_pi (J : Type) [Fintype J] (A : J → Type) [∀ j, CommRing (A j)]
    [∀ j, Algebra K (A j)] [∀ j, Algebra.Etale K (A j)] : Algebra.Etale K (∀ j, A j) :=
  inferInstance

variable {K} in
/-- CHECKED: a tensor product of finite `K`-algebras is finite. -/
theorem finite_tensorProduct (A B : Type) [CommRing A] [Algebra K A] [Module.Finite K A]
    [CommRing B] [Algebra K B] [Module.Finite K B] : Module.Finite K (A ⊗[K] B) :=
  inferInstance

variable {K} in
/-- CHECKED: a tensor product of etale `K`-algebras is etale.

This is *not* found by instance search (`Algebra.Etale` has `baseChange` and `comp` but no
tensor-product instance); the proof composes base change to `A` with etaleness of `K --> A`. -/
theorem etale_tensorProduct (A B : Type) [CommRing A] [Algebra K A] [Algebra.Etale K A]
    [CommRing B] [Algebra K B] [Algebra.Etale K B] :
    Algebra.Etale K (A ⊗[K] B) :=
  Algebra.Etale.comp K A (A ⊗[K] B)

/-! #### 3b. The missing categorical closures

The generic transport machinery is present in Mathlib:

* `CategoryTheory.Limits.createsLimitsOfShapeFullSubcategoryInclusion`
  (`Mathlib/CategoryTheory/Limits/FullSubcategory.lean`) turns
  `[P.IsClosedUnderLimitsOfShape J] [HasLimitsOfShape J C]` into
  `HasLimitsOfShape J P.FullSubcategory`;
* `CategoryTheory.Limits.hasColimitsOfShape_op_of_hasLimitsOfShape`
  (`Mathlib/CategoryTheory/Limits/Opposites.lean`) turns `HasLimitsOfShape J^op C` into
  `HasColimitsOfShape J C^op`;
* `Mathlib/CategoryTheory/ObjectProperty/LimitsOfShape.lean` and
  `.../ColimitsOfShape.lean` contain `ObjectProperty.IsClosedUnderLimitsOfShape` and the
  `prop_limit` API.

So all that is missing for the first two axioms are the instances

  `(CommAlgCat.finiteEtale K).IsClosedUnderLimitsOfShape (Discrete J)`   (J finite)
  `(CommAlgCat.finiteEtale K).IsClosedUnderColimitsOfShape WalkingCospan`

which are *not* in Mathlib: instance search fails at this commit.  By 3a the algebra is there;
what has to be added is the identification of the limit cone in `CommAlgCat K` with the
`Pi`-algebra and of the pushout cocone with the tensor product, then `prop_of_isLimit` /
`prop_of_isColimit` finish the job.
-/

/-- MISSING (Lenstra (G1), pullbacks): `(FiniteEtale K)^op` has pullbacks, i.e. `FiniteEtale K`
has pushouts.

Given `etale_tensorProduct` and `finite_tensorProduct` above, the remaining work is categorical:
identify the pushout of `B <-- A --> C` in `CommAlgCat K` with `B ⊗[A] C` and deduce
`(CommAlgCat.finiteEtale K).IsClosedUnderColimitsOfShape WalkingCospan`. -/
instance hasPullbacks : HasPullbacks (FiniteEtaleAlg K) := sorry

/-- MISSING (Lenstra (G2), finite coproducts): `(FiniteEtale K)^op` has finite coproducts, i.e.
`FiniteEtale K` has finite products.

Given `etale_pi` and `finite_pi` above, the remaining work is categorical: identify the product
cone of a finite family in `CommAlgCat K` with the `Pi`-algebra and deduce
`(CommAlgCat.finiteEtale K).IsClosedUnderLimitsOfShape (Discrete J)`. -/
instance hasFiniteCoproducts : HasFiniteCoproducts (FiniteEtaleAlg K) := sorry


/-- The category of finite etale `K`-algebras (opposite) is a pre-Galois category in the sense
of Lenstra / SGA1.

Only `hasTerminal` is proved.  The remaining four fields are the precise gaps: `hasPullbacks`
and `hasFiniteCoproducts` are reduced in Section 3 to the two `ObjectProperty` closure instances
(the algebra is done, the categorical plumbing is not), while `hasQuotientsByFiniteGroups` and
`monoInducesIsoOnDirectSummand` need mathematics that is not in Mathlib at all.  This instance
must not be used as a hypothesis for statements claimed to be unconditionally formalized. -/
instance instPreGaloisCategory : PreGaloisCategory (FiniteEtaleAlg K) where
  hasTerminal := inferInstance
  hasPullbacks := inferInstance
  hasFiniteCoproducts := inferInstance
  /- MISSING (Lenstra (G2)): quotients by finite groups.
  In `(FiniteEtale K)^op` this is the limit over `SingleObj G` in `FiniteEtale K` of a finite
  group action, i.e. the subalgebra of fixed points `A^G`.  One has to show that `A^G` is finite
  etale over `K` again.  Mathlib has `IntermediateField.fixedField` for fields
  (`Mathlib/FieldTheory/Fixed.lean`) but nothing for finite etale algebras, and no instance of
  `ObjectProperty.IsClosedUnderLimitsOfShape (SingleObj G)`. -/
  hasQuotientsByFiniteGroups := sorry
  /- MISSING (Lenstra (G3)): a monomorphism of the Galois category induces an isomorphism on a
  direct summand.  In `(FiniteEtale K)^op` a monomorphism is an epimorphism of finite etale
  `K`-algebras, and the statement becomes: an epimorphism `A --> B` of finite etale
  `K`-algebras is a projection of a direct product, `A ~= B x C`.  One has to show that
  epimorphisms of finite etale `K`-algebras are surjective and that the kernel of a surjection of
  finite etale algebras is generated by an idempotent.  Nothing of this is in Mathlib. -/
  monoInducesIsoOnDirectSummand := sorry

/-! ### 4. The fibre functor -/

/-- MISSING (Lenstra (G4)-(G6)): the geometric fibre functor `S |-> Hom_K(S, Kbar)` is a fibre
functor.

Its components are:
* `preservesTerminalObjects` -- proved separately as `fiber_self_subsingleton` (the fibre of
  `K` is `Hom_K(K, Kbar)`, a one point set), but not packaged as `PreservesLimitsOfShape`;
* `preservesPullbacks` -- `Hom_K(B (x)_A C, Kbar) ~= Hom_K(B, Kbar) x Hom_K(C, Kbar)` over
  `Hom_K(A, Kbar)`, i.e. `AlgHom` out of a tensor product is a pair of `AlgHom`s (Mathlib has
  `Algebra.TensorProduct.liftEquiv`, but no packaged preservation statement);
* `preservesFiniteCoproducts` -- `Hom_K(A x B, Kbar) ~= Hom_K(A, Kbar) u Hom_K(B, Kbar)`: a
  `K`-algebra map from a product of algebras into a field kills exactly one factor;
* `preservesEpis`; `preservesQuotientsByFiniteGroups` -- the latter is
  `Hom_K(A^G, Kbar) ~= Hom_K(A, Kbar)/G`, i.e. Galois theory over the separably closed field
  `Kbar`, where `Kbar (x)_K A ~= Kbar^n` (`Algebra.FormallyEtale.equivPiOfIsSepClosed`);
* `reflectsIsos` -- a `K`-algebra map that becomes a bijection after `Kbar (x)_K -` is a
  bijection (faithful flatness of `K --> Kbar`).

None of these concrete preservation statements exists in Mathlib; only the separably closed case
is available (`CommAlgCat.FiniteEtale.equivOfIsSepClosed`). -/
instance instFiberFunctor : PreGaloisCategory.FiberFunctor (geometricFiber K) := sorry

/-- A Galois category (Lenstra, Def. 3.1): a pre-Galois category carrying a fibre functor. -/
instance instGaloisCategory : GaloisCategory (FiniteEtaleAlg K) :=
  ⟨geometricFiber K, ⟨inferInstance⟩⟩

/-! ### 5. The Galois correspondence -/

/-- Main theorem (conditional on the missing axioms above).  The category of finite etale
`K`-algebras (opposite) is equivalent to the category of finite sets with a continuous action
of the automorphism group of the geometric fibre functor.

This is `PreGaloisCategory.functorToContAction` of Mathlib
(`Mathlib/CategoryTheory/Galois/Equivalence.lean`, Stacks 0BN4).  Given the `GaloisCategory` and
`FiberFunctor` instances above, this is a complete proof. -/
noncomputable def galoisEquivalence :
    FiniteEtaleAlg K ≌ ContAction FintypeCat (Aut (geometricFiber K)) :=
  (PreGaloisCategory.functorToContAction (geometricFiber K)).asEquivalence

/-! ### 6. Comparison with the absolute Galois group -/

/-- MISSING: the automorphism group of the geometric fibre functor is the absolute Galois group
`Gal(Kbar/K) = Field.absoluteGaloisGroup K`.

Mathematically: a natural automorphism of `A |-> Hom_K(A, Kbar)` is determined by its value on
the identity of a finite subextension `L/K` of `Kbar`, which yields a `K`-embedding
`Kbar --> Kbar`, i.e. an element of `Gal(Kbar/K)`; conversely every such element acts by
post-composition.

Mathlib gaps:
* `Field.absoluteGaloisGroup K` is defined as `AlgebraicClosure K ~=+[K] AlgebraicClosure K`
  with the Krull topology; nothing identifies `Aut` of the fibre functor with it;
* the `Kbar`-valued points live in the ind-category of finite etale `K`-algebras, so one needs
  the pro-representability machinery of
  `Mathlib/CategoryTheory/Galois/Prorepresentability.lean` applied to this particular functor;
* no `AbsoluteGaloisProfinite K : ProfiniteGrp` exists in Mathlib (only the bare topological
  group `Field.absoluteGaloisGroup K`), so the phrase `Action FintypeCat
  (AbsoluteGaloisProfinite K)` of the task has no direct referent; the closest object is
  `ContAction FintypeCat (Aut (geometricFiber K))`.

This statement is recorded as an unproved target, not as a claim. -/
noncomputable def autFiberEquiv :
    Aut (geometricFiber K) ≃* Field.absoluteGaloisGroup K := sorry

/-! ### 7. Sanity check: the separably closed case -/

/-- Over a separably closed field the Galois category of finite etale algebras is literally the
category of finite sets (Mathlib, `CommAlgCat.FiniteEtale.equivOfIsSepClosed`).  This is the
only case in which the Galois correspondence is unconditional in current Mathlib. -/
noncomputable def equivOfIsSepClosed (Ω : Type) [Field Ω] [IsSepClosed Ω] :
    (CommAlgCat.FiniteEtale.{0} Ω)ᵒᵖ ≌ FintypeCat.{0} :=
  CommAlgCat.FiniteEtale.equivOfIsSepClosed Ω

/-- The geometric fibre functor over a separably closed field is an equivalence of categories
(Mathlib instance). -/
noncomputable example (Ω : Type) [Field Ω] [IsSepClosed Ω] :
    (CommAlgCat.FiniteEtale.fiber.{0} Ω Ω).IsEquivalence :=
  inferInstance

end FiniteEtaleAlg

/-! ### 8. Axiom audit

The first six declarations are expected to rest only on `propext`, `Classical.choice`,
`Quot.sound`; the last two are conditional on the `sorry`s of Sections 3b and 4 and therefore
contain `sorryAx`.  This is reported, not hidden. -/

#print axioms S1739FieldEtaleGalois.FiniteEtaleAlg.hom_self_subsingleton
#print axioms S1739FieldEtaleGalois.FiniteEtaleAlg.isTerminal_self
#print axioms S1739FieldEtaleGalois.FiniteEtaleAlg.fiber_self_subsingleton
#print axioms S1739FieldEtaleGalois.FiniteEtaleAlg.finite_pi
#print axioms S1739FieldEtaleGalois.FiniteEtaleAlg.etale_pi
#print axioms S1739FieldEtaleGalois.FiniteEtaleAlg.etale_tensorProduct
#print axioms S1739FieldEtaleGalois.FiniteEtaleAlg.equivOfIsSepClosed
#print axioms S1739FieldEtaleGalois.FiniteEtaleAlg.galoisEquivalence
#print axioms S1739FieldEtaleGalois.FiniteEtaleAlg.autFiberEquiv

end S1739FieldEtaleGalois
