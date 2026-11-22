/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors

# S1767 -- a sorry-free assembly of the Galois category of finite etale `K`-algebras

Target: assemble the actual instances

  `PreGaloisCategory (CommAlgCat.FiniteEtale K)^op`  and  `GaloisCategory (CommAlgCat.FiniteEtale K)^op`

from the **two kernel-checked instances of S1745**

  `S1745.FiniteEtaleClosure.hasPullbacks`            : `HasPullbacks ((CommAlgCat.FiniteEtale K)^op)`
  `S1745.FiniteEtaleClosure.hasFiniteCoproducts`    : `HasFiniteCoproducts ((CommAlgCat.FiniteEtale K)^op)`

plus **exact `Prop` hypotheses** for the fields that are not yet available.  There is no
`sorry`, no new axiom and no changed target anywhere in this file.

## Why this file does not import `S1739FieldEtaleGaloisActual`

`S1739` builds its `PreGaloisCategory`/`FiberFunctor` instances from five `sorry`s, so importing
it would put `sorryAx`-backed instances into the typeclass search space and any declaration of this
file could silently acquire `sorryAx`.  This file imports only S1745 (which is sorry-free: its own
axiom audit is reproduced in Section 6 below) and Mathlib.

## State of the parallel inputs at the time of writing (session S1767, 2026-11-01 00:58)

* S1745: `tmp/sheaf/xif/paper/S1745FiniteEtaleLimitsActual.lean` compiles (EXIT 0) and provides the
  two instances above; its axiom audit lists only `propext`, `Classical.choice`, `Quot.sound`.
  It is the only input that is *used*, and it is used literally (Section 2).
* S1746 (`hasQuotientsByFiniteGroups`): only probe files `_S1746Probe*.lean` exist; there is no
  `S1746...Actual.lean` and no `.olean`.  So there is no result to import and the field is kept as
  the exact `Prop` hypothesis `HasQuotientsByFiniteGroupsField`.
* S1747 (`monoInducesIsoOnDirectSummand`): probes `S1747Probe*.lean` plus the in-flight files
  `S1747Base.lean`, `S1747Part2.lean`, `S1747Full.lean`, `S1747FiniteEtaleMonoSplitActual.lean`
  exist (written 00:56--00:58, none with an `.olean` at the time of writing).  The substantial one, `S1747Full.lean`,
  proves the algebraic core `exists_factor` and the *conditional* transfer
  `monoInducesIsoOnDirectSummand_of_split : FiniteEtaleSplit K -> (G3 field)`; it does not
  discharge the (G3) field unconditionally.  Hence the field is kept as the exact `Prop`
  hypothesis `MonoInducesIsoOnDirectSummandField`; when `FiniteEtaleSplit K` is proved, the field
  is obtained by composing that result with this hypothesis slot (no change to this file).
* S1748: `tmp/sheaf/xif/paper/S1748FiniteEtaleFiberActual.lean` proves the *comparison*
  `Aut (fiber K Omega) ~= (Omega ~=_[K] Omega)` (postcomposition homomorphism, `gHom`, ...).  That is
  **not** one of the six fields of `GaloisCategory`, and the file is not imported here (it provides
  no field of the assembly; it is a later identification of `Aut (geometricFiber K)` with the
  absolute Galois group).
* `S1749FiniteEtaleGaloisAssemblyActual.lean` did the same assembly conditionally on **five**
  hypotheses (it predates S1745).  This file is the upgrade that discharges two of the five from
  S1745 and keeps the remaining three as hypotheses.

## What is in the file

1. Section 1: the category `FiniteEtaleAlg K := (CommAlgCat.FiniteEtale.{0} K)^op`, its terminal
   object `self K = K` and the proof of terminality -- kernel checked, no hypothesis.
2. Section 2: S1745's `hasPullbacks` and `hasFiniteCoproducts` restated at the category used here
   (they are definitionally the same instances; Section 5 checks that the category of this file is
   definitionally S1745's category and that typeclass search finds the instances directly).
3. Section 3: the three remaining fields as *exact* `Prop` abbreviations (no weakening, no added
   assumptions): `HasQuotientsByFiniteGroupsField`, `MonoInducesIsoOnDirectSummandField`,
   `FiberFunctorField`, together with the geometric fibre functor `geometricFiber K`.
4. Section 4: the assembly.  `preGaloisCategory` produces the actual
   `PreGaloisCategory (FiniteEtaleAlg K)` from the two S1745 instances and the two hypotheses;
   `galoisCategory` adds the fibre-functor hypothesis and produces the actual
   `GaloisCategory (FiniteEtaleAlg K)`; `galoisEquivalence` produces Mathlib's
   `PreGaloisCategory.functorToContAction (geometricFiber K)` equivalence.
5. Section 5: consistency checks (`rfl` compatibility with S1745's category, typeclass search
   finding S1745's instances directly).
6. Section 6: axiom audit.  Every declaration below depends only on `propext`,
   `Classical.choice`, `Quot.sound`; in particular no declaration depends on `sorryAx`.

## Verification (session S1767, 2026-11-01 00:58)

* Compile command (from `D:\lean`):
  `lake env lean -j1 -R 'D:\lean' -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1767FiniteEtaleGaloisNoSorryActual.olean tmp/sheaf/xif/paper/S1767FiniteEtaleGaloisNoSorryActual.lean`
  -> EXIT=0, no warnings, no errors (log: `tmp/sheaf/xif/paper/S1767Compile.log`).
* `.olean`: `.lake/build/lib/lean/tmp/sheaf/xif/paper/S1767FiniteEtaleGaloisNoSorryActual.olean`.
* Axiom audit: every `#print axioms` below prints exactly
  `[propext, Classical.choice, Quot.sound]` (hence no `sorryAx`).
* Import check: a downstream file importing this module and applying `preGaloisCategory` and
  `galoisCategory` at the type `(CommAlgCat.FiniteEtale.{0} K)^op` compiles (EXIT=0).
* The file contains no `sorry`/`admit`/`axiom` outside comments and does not import S1739.

## Universe conventions

`K : Type` and `CommAlgCat.FiniteEtale.{0} K`, so `FiniteEtaleAlg K : Type 1` with hom types in
`Type`; this is `Category.{0, 1}`, exactly the universe pair that `GaloisCategory` needs for
`u = 0` (and it is the universe in which S1745 works).  The fibre functor lands in
`FintypeCat.{0}`.

## References

* [lenstraGSchemes]: H. W. Lenstra, *Galois theory for schemes*, Def. 3.1.
* Mathlib, `Mathlib/CategoryTheory/Galois/Basic.lean`, `.../Equivalence.lean`.
* S1745: `tmp/sheaf/xif/paper/S1745FiniteEtaleLimitsActual.lean`.
-/
import tmp.sheaf.xif.paper.S1745FiniteEtaleLimitsActual
import Mathlib.CategoryTheory.Galois.Equivalence
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete

namespace S1767FiniteEtaleGalois

/-! ### 1. The category and its terminal object -/

/-- The opposite of the category of finite etale `K`-algebras: the Galois category of affine
finite etale `K`-schemes.  This is definitionally the category used in S1745. -/
abbrev FiniteEtaleAlg (K : Type) [Field K] : Type 1 := (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ

namespace FiniteEtaleAlg

variable {K : Type} [Field K]

/-- The base field itself, as a finite etale `K`-algebra: the terminal object of the opposite
category (Lenstra (G1)). -/
abbrev self (K : Type) [Field K] : FiniteEtaleAlg K :=
  Opposite.op (CommAlgCat.FiniteEtale.of K K)

/-- Any two morphisms `X ⟶ self K` agree: after removing the opposites they are two `K`-algebra
maps out of `K`, and such maps are unique. -/
theorem hom_self_subsingleton (X : FiniteEtaleAlg K) : Subsingleton (X ⟶ self K) where
  allEq f g := by
    have h : f.unop = g.unop := by
      apply InducedCategory.hom_ext
      apply CommAlgCat.hom_ext
      exact Subsingleton.elim _ _
    exact Quiver.Hom.unop_inj h

instance (X : FiniteEtaleAlg K) : Subsingleton (X ⟶ self K) := hom_self_subsingleton X

/-- The unique morphism `X ⟶ self K`: the structure map `K → A` of the finite etale algebra
`A = X.unop`. -/
instance (X : FiniteEtaleAlg K) : Unique (X ⟶ self K) where
  default := (CommAlgCat.FiniteEtale.ofHom (Algebra.ofId K X.unop.obj)).op
  uniq f := Subsingleton.allEq f _

/-- `K` itself is the terminal object of `(FiniteEtale K)^op` (Lenstra (G1)). -/
def isTerminal_self : IsTerminal (self K) := IsTerminal.ofUnique _

/-- Field 1 of `GaloisCategory`: `(FiniteEtale K)^op` has a terminal object.  Proved here
unconditionally. -/
instance : HasTerminal (FiniteEtaleAlg K) := hasTerminal_of_unique (self K)

end FiniteEtaleAlg

/-! ### 2. The two instances imported from S1745

These are *the same* instances as `S1745.FiniteEtaleClosure.hasPullbacks` and
`S1745.FiniteEtaleClosure.hasFiniteCoproducts`; the theorems below only restate them at the
category abbreviation used in this file, so that the dependence is explicit in the assembly.
(They are also globally registered as instances, so typeclass search finds them directly; see
Section 5.) -/

/-- Field 2 of `GaloisCategory`: `(FiniteEtale K)^op` has pullbacks, i.e. `FiniteEtale K` has
pushouts (which are tensor products over the common vertex).  This is S1745's instance. -/
theorem hasPullbacks_S1745 {K : Type} [Field K] : HasPullbacks (FiniteEtaleAlg K) :=
  S1745.FiniteEtaleClosure.hasPullbacks (K := K)

/-- Field 3 of `GaloisCategory`: `(FiniteEtale K)^op` has finite coproducts, i.e.
`FiniteEtale K` has finite products (which are `Pi`-algebras).  This is S1745's instance. -/
theorem hasFiniteCoproducts_S1745 {K : Type} [Field K] :
    HasFiniteCoproducts (FiniteEtaleAlg K) :=
  S1745.FiniteEtaleClosure.hasFiniteCoproducts (K := K)

/-! ### 3. The remaining fields, as exact `Prop` hypotheses

The three fields below are **not** proved in this file: they are the precise statements that the
parallel work S1746/S1747/S1748 (and its continuation) has to deliver.  Nothing is weakened and
nothing is added: the statements are exactly the corresponding fields of the Mathlib classes,
with the same quantifiers. -/

/-- Field 4 of `GaloisCategory` (Lenstra (G2)): `(FiniteEtale K)^op` has quotients by finite
groups, i.e. for every finite group `G` and every `G`-action on a finite etale `K`-algebra `A`
the fixed point algebra `A^G` is again finite etale and is the limit of the action diagram.

This is the exact first argument expected by `PreGaloisCategory.hasQuotientsByFiniteGroups`
(`G : Type 0` because `FiniteEtaleAlg K : Type 1` with `Category.{0, 1}`). -/
abbrev HasQuotientsByFiniteGroupsField (K : Type) [Field K] : Prop :=
  ∀ (G : Type) [Group G] [Finite G], HasColimitsOfShape (SingleObj G) (FiniteEtaleAlg K)

/-- Field 5 of `GaloisCategory` (Lenstra (G3)): every monomorphism in `(FiniteEtale K)^op`
induces an isomorphism on a direct summand.

This is the exact second argument expected by
`PreGaloisCategory.monoInducesIsoOnDirectSummand` (the class takes `Mono i` as an instance
argument; the proposition below takes it as an explicit argument, which is the same type). -/
abbrev MonoInducesIsoOnDirectSummandField (K : Type) [Field K] : Prop :=
  ∀ {X Y : FiniteEtaleAlg K} (i : X ⟶ Y), Mono i →
    ∃ (Z : FiniteEtaleAlg K) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u))

/-- The geometric fibre functor `S ↦ Hom_K(S, Kbar)` at the algebraic closure of `K`.  This is
Mathlib's `CommAlgCat.FiniteEtale.fiber K (AlgebraicClosure K)`; no new functor is invented. -/
abbrev geometricFiber (K : Type) [Field K] : FiniteEtaleAlg K ⥤ FintypeCat.{0} :=
  CommAlgCat.FiniteEtale.fiber K (AlgebraicClosure K)

/-- Field 6 of `GaloisCategory` (Lenstra (G4)--(G6)): the geometric fibre functor is a fibre
functor.  The six sub-fields of `PreGaloisCategory.FiberFunctor` are
`preservesTerminalObjects`, `preservesPullbacks`, `preservesFiniteCoproducts`, `preservesEpis`,
`preservesQuotientsByFiniteGroups` and `reflectsIsos`.

The hypothesis is stated at the `PreGaloisCategory` instance produced by `preGaloisCategory`
below, so that the assembly can pass the instance explicitly. -/
abbrev FiberFunctorField (K : Type) [Field K]
    (hPre : PreGaloisCategory (FiniteEtaleAlg K)) : Prop :=
  @PreGaloisCategory.FiberFunctor (FiniteEtaleAlg K) _ hPre (geometricFiber K)

/-! ### 4. Assembly -/

variable {K : Type} [Field K]

/-- **Assembly, step 1.**  The two S1745 instances and the two `Prop` hypotheses turn
`(FiniteEtale K)^op` into a pre-Galois category.  No `sorry`: the terminal object is proved in
Section 1, pullbacks and finite coproducts are S1745's instances, and the remaining two fields are
the explicit hypotheses. -/
theorem preGaloisCategory
    (hQuot : HasQuotientsByFiniteGroupsField K)
    (hMono : MonoInducesIsoOnDirectSummandField K) :
    PreGaloisCategory (FiniteEtaleAlg K) where
  hasTerminal := inferInstance
  hasPullbacks := hasPullbacks_S1745 (K := K)
  hasFiniteCoproducts := hasFiniteCoproducts_S1745 (K := K)
  hasQuotientsByFiniteGroups := hQuot
  monoInducesIsoOnDirectSummand := hMono

/-- **Assembly, step 2.**  Adding the fibre-functor hypothesis, the six fields together turn
`(FiniteEtale K)^op` into a Galois category.  The fibre functor of the `GaloisCategory` instance is
`geometricFiber K`, not an arbitrary `Classical.choose` of one: the field `hasFiberFunctor`
is fed explicitly.

Note that `PreGaloisCategory.FiberFunctor` is a class living in `Prop`, so the `PreGaloisCategory`
instance used inside `hFiber` is propositionally (and here even definitionally) the one built by
`preGaloisCategory`. -/
theorem galoisCategory
    (hQuot : HasQuotientsByFiniteGroupsField K)
    (hMono : MonoInducesIsoOnDirectSummandField K)
    (hFiber : FiberFunctorField K (preGaloisCategory (K := K) hQuot hMono)) :
    GaloisCategory (FiniteEtaleAlg K) := by
  letI : PreGaloisCategory (FiniteEtaleAlg K) := preGaloisCategory hQuot hMono
  exact GaloisCategory.mk ⟨geometricFiber K, ⟨hFiber⟩⟩

/-- **Assembly, step 3.**  The main theorem of Galois theory for finite etale `K`-algebras:
`(FiniteEtale K)^op` is equivalent to finite sets with a continuous action of the automorphism
group of the geometric fibre functor.

This is Mathlib's `PreGaloisCategory.functorToContAction` (Stacks 0BN4); the definition is literally
its `asEquivalence`, so the functor of the equivalence is the geometric fibre functor `geometricFiber K`
and nothing is postulated. -/
noncomputable def galoisEquivalence
    (hQuot : HasQuotientsByFiniteGroupsField K)
    (hMono : MonoInducesIsoOnDirectSummandField K)
    (hFiber : FiberFunctorField K (preGaloisCategory (K := K) hQuot hMono)) :
    FiniteEtaleAlg K ≌ ContAction FintypeCat (Aut (geometricFiber K)) := by
  letI : PreGaloisCategory (FiniteEtaleAlg K) := preGaloisCategory hQuot hMono
  letI : PreGaloisCategory.FiberFunctor (geometricFiber K) := hFiber
  letI : GaloisCategory (FiniteEtaleAlg K) := galoisCategory hQuot hMono hFiber
  exact (PreGaloisCategory.functorToContAction (geometricFiber K)).asEquivalence

/-- The assembly in the shape in which a consumer with the five field hypotheses of S1749 meets it:
if one passes pullbacks and finite coproducts explicitly (as S1749 did), the result agrees with the
assembly above, because the explicit instances are S1745's instances.  This theorem only records
that no information was lost; it is not used by the assembly. -/
theorem preGaloisCategory_of_explicit
    (hPull : HasPullbacks (FiniteEtaleAlg K))
    (hCoprod : HasFiniteCoproducts (FiniteEtaleAlg K))
    (hQuot : HasQuotientsByFiniteGroupsField K)
    (hMono : MonoInducesIsoOnDirectSummandField K) :
    PreGaloisCategory (FiniteEtaleAlg K) where
  hasTerminal := inferInstance
  hasPullbacks := hPull
  hasFiniteCoproducts := hCoprod
  hasQuotientsByFiniteGroups := hQuot
  monoInducesIsoOnDirectSummand := hMono

/-! ### 5. Consistency checks

These are checks performed at elaboration time (they are part of what a successful compile of this
file certifies). -/

/-- The category of this file is S1745's category, definitionally. -/
example : (S1745.FiniteEtaleAlg K : Type 1) = (FiniteEtaleAlg K : Type 1) := rfl

/-- Typeclass search finds S1745's pullback instance for the category of this file. -/
example : HasPullbacks (FiniteEtaleAlg K) := inferInstance

/-- Typeclass search finds S1745's finite-coproduct instance for the category of this file. -/
example : HasFiniteCoproducts (FiniteEtaleAlg K) := inferInstance

/-- The terminal object of Section 1 is a terminal object. -/
example : IsTerminal (FiniteEtaleAlg.self K) := FiniteEtaleAlg.isTerminal_self

/-- **Target check 1** (the exact statement of the task): the pre-Galois category instance, for the
category written as `(CommAlgCat.FiniteEtale K)^op` and not merely at the file-local abbreviation. -/
example (hQuot : HasQuotientsByFiniteGroupsField K)
    (hMono : MonoInducesIsoOnDirectSummandField K) :
    PreGaloisCategory ((CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) :=
  preGaloisCategory hQuot hMono

/-- **Target check 2** (the exact statement of the task): the Galois category instance, for the
category written as `(CommAlgCat.FiniteEtale K)^op`. -/
example (hQuot : HasQuotientsByFiniteGroupsField K)
    (hMono : MonoInducesIsoOnDirectSummandField K)
    (hFiber : FiberFunctorField K (preGaloisCategory (K := K) hQuot hMono)) :
    GaloisCategory ((CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) :=
  galoisCategory hQuot hMono hFiber

/-! ### 6. Axiom audit

All declarations of this file, and the S1745 instances they use, are expected to depend only on
`propext`, `Classical.choice` and `Quot.sound`.  In particular none of them depends on
`sorryAx`: the three open fields enter as explicit hypotheses only. -/

#print axioms S1745.FiniteEtaleClosure.hasPullbacks
#print axioms S1745.FiniteEtaleClosure.hasFiniteCoproducts

#print axioms S1767FiniteEtaleGalois.FiniteEtaleAlg.hom_self_subsingleton
#print axioms S1767FiniteEtaleGalois.FiniteEtaleAlg.isTerminal_self
#print axioms S1767FiniteEtaleGalois.hasPullbacks_S1745
#print axioms S1767FiniteEtaleGalois.hasFiniteCoproducts_S1745
#print axioms S1767FiniteEtaleGalois.preGaloisCategory
#print axioms S1767FiniteEtaleGalois.galoisCategory
#print axioms S1767FiniteEtaleGalois.galoisEquivalence
#print axioms S1767FiniteEtaleGalois.preGaloisCategory_of_explicit

end S1767FiniteEtaleGalois
