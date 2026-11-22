/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# S1749 -- assembling `GaloisCategory (CommAlgCat.FiniteEtale K)^op`

Task: on the basis of S1739 (and of the in-flight S1745--S1748 work on the six
`GaloisCategory` fields), assemble the *actual* instance

  `GaloisCategory ((CommAlgCat.FiniteEtale K)^op)`

and the equivalence

  `PreGaloisCategory.functorToContAction (geometricFiber K) :`
  `((FiniteEtale K)^op) ~= ContAction FintypeCat (Aut (geometricFiber K))`

for an arbitrary field `K`; list precisely which fields are still missing, and
do not use `sorry` anywhere.

## State of the inputs at the time of writing (session S1749)

* `S1739FieldEtaleGaloisActual.lean` exists and compiles, but its
  `PreGaloisCategory`/`FiberFunctor` instances are built from **five sorries**
  (`hasPullbacks`, `hasFiniteCoproducts`, `hasQuotientsByFiniteGroups`,
  `monoInducesIsoOnDirectSummand`, `instFiberFunctor`); it also carries a
  sorry for `autFiberEquiv`.  Its kernel-checked part is exactly: the category,
  the terminal object, the fibre functor and the value of the fibre functor at
  the terminal object, plus the algebraic closures `finite_pi`, `etale_pi`,
  `finite_tensorProduct`, `etale_tensorProduct`.
* The in-flight S1745--S1748 work was, at the time of writing (2026-11-01,~
  00:30), still at the probe stage: the directory contains
  `S1745Probe0-5`, `S1746Probe0-2`, `S1747Probe1-5`, `S1748Probe0-5`,
  `_S1746Probe*`, `_S1748Probe*` and one non-probe file
  `S1748FiniteEtaleFiberActual.lean`.  The latter attacks the comparison
  `Aut (fiber K Omega) ≃* (Omega ≃ₐ[K] Omega)` -- the identification of the
  automorphism group of the geometric fibre with the absolute Galois group --
  and not the `PreGaloisCategory.FiberFunctor` instance; it does not provide
  any of the six fields assembled here.  A grep over
  `tmp/sheaf/xif/paper/` finds no instance of any of the five open fields
  other than the five `sorry`s of S1739.

  So at present there is **no imported instance for any of the five open
  fields**.  Because of that this file is self-contained (Mathlib imports
  only) and does *not* import S1739: importing it would put the five
  sorry-backed instances into the typeclass search space, and any theorem
  proved here could silently acquire `sorryAx`.
* Relation to S1748: the `Aut` comparison of S1748 is *not* one of the six
  fields; it is a further identification after the assembly here.  The target
  of `galoisEquivalence` below is already stated with `Aut (geometricFiber K)`,
  so S1748's comparison can be composed with it once both are available.
* The file therefore assembles the structure *conditionally on the six fields*
  and records the five open fields, with their exact statements, in Section 5.

## What this file does

1. Sets up `FiniteEtaleAlg K := (CommAlgCat.FiniteEtale.{u} K)^op` with its
   `Category.{u, u+1}` instance, the terminal object `self K = K` and the proof
   of terminality -- *kernel checked, no sorry*.
2. Sets up the geometric fibre functor `fiber K Omega`,
   `geometricFiber K = fiber K (AlgebraicClosure K)`, and proves that the fibre
   of `K` is a subsingleton -- *kernel checked, no sorry*.
3. States the **six fields** of `GaloisCategory` one by one, as named
   `Prop`-valued abbreviations, with a docstring saying what is proved, what is
   missing, and what the remaining mathematical content is.
4. Proves, from the six fields as explicit hypotheses (no sorry, no axioms
   beyond the three standard ones), the actual instance
   `PreGaloisCategory (FiniteEtaleAlg K)`, the actual instance
   `GaloisCategory (FiniteEtaleAlg K)`, and the actual
   `PreGaloisCategory.functorToContAction` equivalence.  The axiom audit at the
   end of the file shows that these theorems carry no `sorryAx`.
5. Records, as machine-checkable data, exactly which hypotheses are missing
   (`fieldStatus`, `missingFields`), so that filling in S1745--S1748 is a matter
   of replacing five hypotheses by five instances **with the same statements**.

## Universe conventions

`K : Type u` and the algebras live in `CommAlgCat.{u} K` (objects are algebras
with carrier in `Type u`), so `FiniteEtaleAlg K : Type (u+1)` with hom types in
`Type u`.  This is exactly the universe pair that `GaloisCategory` expects, and
the fibre functor lands in `FintypeCat.{u}`.  For `u = 0` this is literally
`GaloisCategory (CommAlgCat.FiniteEtale K)^op` with `CommAlgCat.FiniteEtale K`
in the default universe.

## References

* [lenstraGSchemes]: H. W. Lenstra, *Galois theory for schemes*, Def. 3.1.
* Mathlib, `Mathlib/CategoryTheory/Galois/{Basic,Equivalence}.lean`.
* Mathlib, `Mathlib/RingTheory/Etale/Finite.lean` (C. Merten, 2026).
-/
import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Equivalence
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.SingleObj

universe u

open CategoryTheory CategoryTheory.Limits

open scoped FintypeCatDiscrete

namespace S1749FiniteEtaleGaloisAssembly

variable (K : Type u) [Field K]

/-! ### 1. The category -/

/-- The opposite of the category of finite etale `K`-algebras.

This is the Galois category of (affine) finite etale `K`-schemes, i.e. of
`Spec`s of finite etale `K`-algebras, with the opposite taken so that the
geometric fibre functor `S |-> Hom_K(S, Kbar)` is covariant and `K` (the
initial finite etale `K`-algebra) is terminal (Lenstra (G1)).

The carrier of an object is in `Type u` and the hom types are in `Type u`, so
this is a `Category.{u, u+1}`. -/
abbrev FiniteEtaleAlg : Type (u + 1) := (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ

namespace FiniteEtaleAlg

instance category : Category.{u, u + 1} (FiniteEtaleAlg K) := inferInstance

/-- A finite etale `K`-algebra, bundled as an object of the opposite category. -/
abbrev of (A : Type u) [CommRing A] [Algebra K A] [Module.Finite K A] [Algebra.Etale K A] :
    FiniteEtaleAlg K :=
  Opposite.op (CommAlgCat.FiniteEtale.of K A)

/-- The base field itself, as a finite etale `K`-algebra: the terminal object. -/
abbrev self : FiniteEtaleAlg K := of K K

variable {K} in
/-- Every `K`-algebra map `K --> A` is the structure map: `K` is initial in
`FiniteEtale K`, hence terminal in the opposite category. -/
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

/-- The geometric fibre functor `S |-> Hom_K(S, Omega)` for a geometric point
`Omega` of `K`; this is `CommAlgCat.FiniteEtale.fiber`. -/
noncomputable abbrev fiber (Ω : Type u) [Field Ω] [Algebra K Ω] :
    FiniteEtaleAlg K ⥤ FintypeCat.{u} :=
  CommAlgCat.FiniteEtale.fiber K Ω

/-- The geometric fibre functor at the geometric point given by an algebraic
closure of `K`. -/
noncomputable abbrev geometricFiber : FiniteEtaleAlg K ⥤ FintypeCat.{u} :=
  fiber K (AlgebraicClosure K)

variable {K} in
/-- The fibre of the base field is a one point set: the fibre functor preserves
the terminal object (the easy half of Lenstra (G4)). -/
theorem fiber_self_subsingleton (Ω : Type u) [Field Ω] [Algebra K Ω] :
    Subsingleton (↥((fiber K Ω).obj (self K))) := by
  change Subsingleton (K →ₐ[K] Ω)
  infer_instance

/-! ### 3. The six fields of `GaloisCategory`, one by one

`GaloisCategory C` has six fields: the five axioms (G1)--(G3) of a pre-Galois
category (`hasTerminal`, `hasPullbacks`, `hasFiniteCoproducts`,
`hasQuotientsByFiniteGroups`, `monoInducesIsoOnDirectSummand`) and the
existence of a fibre functor (`hasFiberFunctor`, whose content is the six
fields (G4)--(G6) of `PreGaloisCategory.FiberFunctor`).

Below, the five open fields are named as `Prop`-valued abbreviations carrying
the *exact* statement that must eventually become an instance, followed by the
algebraic reformulation that the proof has to establish.  Field 1 is proved
above, unconditionally. -/

/-- **Field 1** (Lenstra (G1)): `(FiniteEtale K)^op` has a terminal object.

PROVED unconditionally in this file: `FiniteEtaleAlg.self K` with
`FiniteEtaleAlg.isTerminal_self` and the instance
`FiniteEtaleAlg.hasTerminal`. -/
abbrev HasTerminalField : Prop := HasTerminal (FiniteEtaleAlg K)

/-- **Field 2** (Lenstra (G1)): `(FiniteEtale K)^op` has pullbacks, i.e.
`FiniteEtale K` has pushouts.

MISSING.  The algebraic content is available: for `A --> B`, `A --> C` finite
etale `K`-algebras, the pushout in `CommAlgCat K` is the tensor product
`B (x)_A C`; it is finite over `K` (base change of a finite module over `A`,
which is finite over `K`) and etale over `K` (`Algebra.Etale.baseChange` along
`A --> C` composed with `Algebra.Etale.comp` for `C/K`; note that
`Algebra.Etale` is *not* in general stable under `A --> B` for `A` not etale
over `K`, so the proof must use `C` as the base).  The categorical content --
identifying the pushout cocone in `CommAlgCat K` with the tensor product and
deducing `(CommAlgCat.finiteEtale K).IsClosedUnderColimitsOfShape
WalkingCospan` -- is not in Mathlib.

Equivalently (this is what the Mathlib plumbing wants):
`(CommAlgCat.finiteEtale.{u} K).IsClosedUnderColimitsOfShape WalkingCospan`,
which gives `HasColimitsOfShape WalkingCospan (CommAlgCat.FiniteEtale K)` by
`CategoryTheory.Limits.hasColimitsOfShape_of_closedUnderColimits`, hence
`HasLimitsOfShape WalkingCospan (FiniteEtaleAlg K)`. -/
abbrev HasPullbacksField : Prop := HasPullbacks (FiniteEtaleAlg K)

/-- **Field 3** (Lenstra (G2)): `(FiniteEtale K)^op` has finite coproducts,
i.e. `FiniteEtale K` has finite products.

MISSING.  The algebraic content is available: the product of a finite family
of finite etale `K`-algebras is the `Pi`-algebra, which is finite
(`Module.Finite` of a finite product) and etale (`Algebra.FormallyEtale.pi_iff`
/ `Algebra.Etale.pi`); S1739 proved these as `finite_pi`, `etale_pi`.  What is
missing is the categorical identification of the product cone in
`CommAlgCat K` with the `Pi`-algebra, giving
`(CommAlgCat.finiteEtale K).IsClosedUnderLimitsOfShape (Discrete J)` for
finite `J`. -/
abbrev HasFiniteCoproductsField : Prop := HasFiniteCoproducts (FiniteEtaleAlg K)

/-- **Field 4** (Lenstra (G2)): `(FiniteEtale K)^op` has quotients by finite
groups.

MISSING.  In `(FiniteEtale K)^op` this is the limit over `SingleObj G` in
`FiniteEtale K` of a finite group action, i.e. the fixed point subalgebra
`A^G` of a finite etale `K`-algebra `A` under a finite group `G` acting by
`K`-algebra automorphisms.  One has to prove that `A^G` is finite etale over
`K` again (Galois descent: after base change to `Kbar`, `A` becomes `Kbar^n`
with `G` acting by permuting the factors, so `A^G` becomes `Kbar^m`; then
descend finiteness and etaleness along the faithfully flat extension
`K --> Kbar`).  Mathlib has `IntermediateField.fixedField` for subfields but
nothing for finite etale algebras, and no instance of
`ObjectProperty.IsClosedUnderLimitsOfShape (SingleObj G)`.

The shape bookkeeping is: a `G`-action on `A` in `FiniteEtale K` is a functor
`SingleObj G ⥤ FiniteEtale K`; the limit of that diagram in `FiniteEtale K` is
the object we want, and the colimit in the opposite category is what
`hasQuotientsByFiniteGroups` asks for. -/
abbrev HasQuotientsByFiniteGroupsField : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    HasColimitsOfShape (SingleObj G) (FiniteEtaleAlg K)

/-- **Field 5** (Lenstra (G3)): every monomorphism in `(FiniteEtale K)^op`
induces an isomorphism on a direct summand.

MISSING.  A monomorphism in `(FiniteEtale K)^op` is an epimorphism in
`FiniteEtale K`; the statement to prove is that an epimorphism `A --> B` of
finite etale `K`-algebras exhibits `A` as a direct factor `B x C` of `B`.
This needs: epimorphisms of finite etale `K`-algebras are surjective, and the
kernel of such a surjection is generated by an idempotent (true since a finite
etale `K`-algebra is a finite product of finite separable field extensions:
a surjection onto a product of fields splits).  Mathlib has neither statement
for finite etale algebras. -/
abbrev MonoInducesIsoOnDirectSummandField : Prop :=
  ∀ {X Y : FiniteEtaleAlg K} (i : X ⟶ Y), Mono i →
    ∃ (Z : FiniteEtaleAlg K) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u))

/-- **Field 6** (Lenstra (G4)--(G6)): the geometric fibre functor
`S |-> Hom_K(S, Kbar)` is a fibre functor.

MISSING.  The six sub-fields of `PreGaloisCategory.FiberFunctor` are:
* `preservesTerminalObjects`: the fibre of `K` is a point (proved above as
  `fiber_self_subsingleton`, but not packaged as preservation of limits of
  shape `Discrete PEmpty`);
* `preservesPullbacks`: `Hom_A(B (x)_A C, Kbar) ~= Hom_A(B, Kbar) x_{Hom(A,Kbar)}
  Hom_A(C, Kbar)`, from `Algebra.TensorProduct.liftEquiv`;
* `preservesFiniteCoproducts`: a `K`-algebra map from a finite product of
  `K`-algebras into the field `Kbar` kills all but one factor, so
  `Hom_K(A x B, Kbar) ~= Hom_K(A, Kbar) u Hom_K(B, Kbar)`;
* `preservesEpis`: a monomorphism of finite etale `K`-algebras is injective,
  and every `K`-embedding of a finite etale algebra into `Kbar` extends along
  an injection (separability), so the induced map on fibres is surjective;
* `preservesQuotientsByFiniteGroups`: for a finite group `G` acting on `A`,
  `Hom_K(A^G, Kbar) ~= Hom_K(A, Kbar)/G`;
* `reflectsIsos`: an algebra map that becomes a bijection after
  `Kbar (x)_K -` is a bijection (faithful flatness of `K --> Kbar`, plus
  `CommAlgCat.FiniteEtale.fiberIsoBaseChangeFiber` and the separably closed
  case `CommAlgCat.FiniteEtale.equivOfIsSepClosed`).

Mathlib has only the separably closed case (`equivOfIsSepClosed`) and the base
change formula for fibres (`fiberIsoBaseChangeFiber`, `fiberIsoComp`); none of
the six preservation statements is stated. -/
abbrev FiberFunctorField (hPre : PreGaloisCategory (FiniteEtaleAlg K)) : Prop :=
  @PreGaloisCategory.FiberFunctor (FiniteEtaleAlg K) _ hPre (geometricFiber K)

/-! ### 4. Assembly

The following theorems are the actual assembly: from the six fields (five
hypotheses plus the fibre functor) they produce the actual
`PreGaloisCategory` instance, the actual `GaloisCategory` instance and the
actual `functorToContAction` equivalence.  No sorry is involved; the axiom
audit in Section 6 shows that the only axioms used are `propext`,
`Classical.choice` and `Quot.sound`. -/

section Assembly

variable {K}

/-- **Assembly, step 1.** The five axioms (G1)--(G3) turn `(FiniteEtale K)^op`
into a pre-Galois category.

The hypothesis `hQuot` is `HasQuotientsByFiniteGroupsField` and `hMono` is the
explicit form of `MonoInducesIsoOnDirectSummandField` (the class field takes
`[Mono i]` as an instance, the hypothesis takes it as an argument). -/
theorem preGaloisCategory
    (hPull : HasPullbacks (FiniteEtaleAlg K))
    (hCoprod : HasFiniteCoproducts (FiniteEtaleAlg K))
    (hQuot : ∀ (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G) (FiniteEtaleAlg K))
    (hMono : ∀ {X Y : FiniteEtaleAlg K} (i : X ⟶ Y), Mono i →
      ∃ (Z : FiniteEtaleAlg K) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u))) :
    PreGaloisCategory (FiniteEtaleAlg K) where
  hasTerminal := inferInstance
  hasPullbacks := hPull
  hasFiniteCoproducts := hCoprod
  hasQuotientsByFiniteGroups := hQuot
  monoInducesIsoOnDirectSummand := hMono

/-- **Assembly, step 2.** The six fields together turn `(FiniteEtale K)^op`
into a Galois category. -/
theorem galoisCategory
    (hPull : HasPullbacks (FiniteEtaleAlg K))
    (hCoprod : HasFiniteCoproducts (FiniteEtaleAlg K))
    (hQuot : ∀ (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G) (FiniteEtaleAlg K))
    (hMono : ∀ {X Y : FiniteEtaleAlg K} (i : X ⟶ Y), Mono i →
      ∃ (Z : FiniteEtaleAlg K) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u)))
    (hFiber : FiberFunctorField (K := K) (preGaloisCategory hPull hCoprod hQuot hMono)) :
    GaloisCategory (FiniteEtaleAlg K) := by
  letI : PreGaloisCategory (FiniteEtaleAlg K) :=
    preGaloisCategory hPull hCoprod hQuot hMono
  exact GaloisCategory.mk ⟨geometricFiber K, ⟨hFiber⟩⟩

/-- **Assembly, step 3.** The main theorem of Galois theory for finite etale
`K`-algebras: `(FiniteEtale K)^op` is equivalent to the category of finite sets
with a continuous action of the automorphism group of the geometric fibre
functor.

This is Mathlib's `PreGaloisCategory.functorToContAction`
(`Mathlib/CategoryTheory/Galois/Equivalence.lean`, Stacks 0BN4), which is an
equivalence as soon as the six fields are available.  The statement is the
equivalence itself; nothing is postulated. -/
noncomputable def galoisEquivalence
    (hPull : HasPullbacks (FiniteEtaleAlg K))
    (hCoprod : HasFiniteCoproducts (FiniteEtaleAlg K))
    (hQuot : ∀ (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G) (FiniteEtaleAlg K))
    (hMono : ∀ {X Y : FiniteEtaleAlg K} (i : X ⟶ Y), Mono i →
      ∃ (Z : FiniteEtaleAlg K) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u)))
    (hFiber : FiberFunctorField (K := K) (preGaloisCategory hPull hCoprod hQuot hMono)) :
    FiniteEtaleAlg K ≌ ContAction FintypeCat (Aut (geometricFiber K)) := by
  letI : PreGaloisCategory (FiniteEtaleAlg K) :=
    preGaloisCategory hPull hCoprod hQuot hMono
  letI : PreGaloisCategory.FiberFunctor (geometricFiber K) := hFiber
  letI : GaloisCategory (FiniteEtaleAlg K) :=
    GaloisCategory.mk ⟨geometricFiber K, ⟨hFiber⟩⟩
  exact (PreGaloisCategory.functorToContAction (geometricFiber K)).asEquivalence

/-! The functor underlying `galoisEquivalence` is, by construction, Mathlib's
`PreGaloisCategory.functorToContAction (geometricFiber K)` -- the definition
above is literally `(functorToContAction (geometricFiber K)).asEquivalence`, so
the functor of the assembled equivalence is that functor (`rfl`) and no functor
was invented in the assembly.  We do not restate this as a separate theorem,
because the statement would have to name the `PreGaloisCategory` instance
argument of `functorToContAction` explicitly. -/

end Assembly

/-! ### 4b. How the five missing fields plug in

If the five open fields are available (as instances, which is the shape in
which S1745--S1748 will deliver them, and the shape that the `Prop`
abbreviations of Section 3 name), then `preGaloisCategory` and `galoisCategory`
above apply directly: `hPull` and `hCoprod` are the two limit instances,
`hQuot` is the function `G |-> hasQuotientsByFiniteGroups G`, and `hFiber` is
the fibre functor.  No further data is needed, and nothing has to change in
the statements.

Two empirical remarks, both observed while writing this file:

* the raw (G3) statement is *not* a class type (its head is `Exists`, not a
  class), so Lean rejects instance binders of that shape.  To expose (G3) as an
  instance one has to wrap it in a class, e.g.  `class
  MonoInducesIsoOnDirectSummand (C) [Category C] : Prop` with a single field of
  the (G3) shape; the `hMono` hypothesis of Section 4 is exactly that field,
  passed as a function, so nothing is lost;
* `PreGaloisCategory` is a `Prop`-valued class, so its instances are
  propositionally equal; which instance appears as the implicit argument of
  `PreGaloisCategory.FiberFunctor` is therefore immaterial mathematically.  At
  an integration site where the definitional equality is not found
  automatically, pass the instance explicitly, as this file does via
  `preGaloisCategory hPull hCoprod hQuot hMono`. -/

/-! ### 5. The exact list of missing fields -/

/-- The six fields of `GaloisCategory (FiniteEtale K)^op` together with their
status in this file.  `true` means proved unconditionally here; the other
entries are the fields that still have to be supplied as instances.  This is
data, not an assertion of completeness: the assembly theorems above take the
missing ones as hypotheses. -/
structure FieldStatus where
  /-- Whether field 1 (`hasTerminal`) is available unconditionally. -/
  hasTerminal_proved : Bool
  /-- Whether field 2 (`hasPullbacks`) is available unconditionally. -/
  hasPullbacks_proved : Bool
  /-- Whether field 3 (`hasFiniteCoproducts`) is available unconditionally. -/
  hasFiniteCoproducts_proved : Bool
  /-- Whether field 4 (`hasQuotientsByFiniteGroups`) is available unconditionally. -/
  hasQuotientsByFiniteGroups_proved : Bool
  /-- Whether field 5 (`monoInducesIsoOnDirectSummand`) is available unconditionally. -/
  monoInducesIsoOnDirectSummand_proved : Bool
  /-- Whether field 6 (`FiberFunctor (geometricFiber K)`) is available unconditionally. -/
  fiberFunctor_proved : Bool

/-- The status of the six fields at the end of session S1749: exactly one of the
six is proved; the other five are the precise `Prop`s of Section 3. -/
def fieldStatus : FieldStatus where
  hasTerminal_proved := true
  hasPullbacks_proved := false
  hasFiniteCoproducts_proved := false
  hasQuotientsByFiniteGroups_proved := false
  monoInducesIsoOnDirectSummand_proved := false
  fiberFunctor_proved := false

/-- The missing fields, as the exact `Prop`s that have to be turned into
instances, in the order of the six fields of `GaloisCategory`; field 1 is
absent because it is proved. -/
def missingFields : List String :=
  ["HasPullbacks (FiniteEtaleAlg K)",
   "HasFiniteCoproducts (FiniteEtaleAlg K)",
   "∀ (G : Type u) [Group G] [Finite G], HasColimitsOfShape (SingleObj G) (FiniteEtaleAlg K)",
   "∀ {X Y : FiniteEtaleAlg K} (i : X ⟶ Y), Mono i → ∃ Z u, Nonempty (IsColimit (BinaryCofan.mk i u))",
   "PreGaloisCategory.FiberFunctor (geometricFiber K)"]

/-- Sanity check: the list of missing fields has five entries, i.e. exactly the
five fields not proved in this file. -/
theorem missingFields_length : missingFields.length = 5 := rfl

/-! ### 6. Axiom audit

Every declaration below is expected to rest only on `propext`,
`Classical.choice` and `Quot.sound`.  In particular none of them rests on
`sorryAx`: the five missing fields enter as explicit hypotheses of the assembly
theorems, never as axioms. -/

#print axioms S1749FiniteEtaleGaloisAssembly.FiniteEtaleAlg.hom_self_subsingleton
#print axioms S1749FiniteEtaleGaloisAssembly.FiniteEtaleAlg.isTerminal_self
#print axioms S1749FiniteEtaleGaloisAssembly.FiniteEtaleAlg.fiber_self_subsingleton
#print axioms S1749FiniteEtaleGaloisAssembly.FiniteEtaleAlg.preGaloisCategory
#print axioms S1749FiniteEtaleGaloisAssembly.FiniteEtaleAlg.galoisCategory
#print axioms S1749FiniteEtaleGaloisAssembly.FiniteEtaleAlg.galoisEquivalence

end FiniteEtaleAlg

end S1749FiniteEtaleGaloisAssembly
