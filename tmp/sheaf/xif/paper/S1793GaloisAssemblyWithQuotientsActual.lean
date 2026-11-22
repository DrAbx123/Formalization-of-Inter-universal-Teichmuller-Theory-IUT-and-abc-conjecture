/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors

# S1793 -- integrated Galois assembly for finite etale K-algebras: (G2) is actual

This file is the **integration** of three parallel developments:

* S1745FiniteEtaleLimitsActual   -- kernel-checked hasPullbacks / hasFiniteCoproducts
  of (CommAlgCat.FiniteEtale K)^op (tensor products and Pi-algebras),
* S1767FiniteEtaleGaloisNoSorryActual -- sorry-free assembly of the pre-Galois category,
  with a proved terminal object and the two S1745 instances, and the remaining fields as
  exact Prop hypotheses,
* S1770FiniteEtaleFixedPointsActual -- unconditional (G2): for every finite group G,
  (FiniteEtale K)^op has colimits of shape SingleObj G, given by the invariant
  subalgebra A^G (S1770.FiniteEtaleAlg.hasQuotientsByFiniteGroups).

The result is a PreGaloisCategory (FiniteEtaleAlg K) in which **four of the five fields are
actual kernel-checked proofs**:

  field                             source                          status
  ---------------------------------------------------------------------------
  hasTerminal                       S1767 section 1 (K itself)      actual
  hasPullbacks                      S1745 (hasPullbacks)            actual
  hasFiniteCoproducts               S1745 (hasFiniteCoproducts)     actual
  hasQuotientsByFiniteGroups        S1770 (invariant subalgebra)    actual
  monoInducesIsoOnDirectSummand     --                              hypothesis (G3)

and then a GaloisCategory (FiniteEtaleAlg K) from the single remaining hypothesis (G3)
together with a fibre-functor hypothesis for the geometric fibre functor.

There is no sorry, no admit, no new axiom and no changed target in this file: the only
hypotheses are the exact remaining fields, and they are explicit arguments of the theorems.
In particular this file does **not** import S1739FieldEtaleGaloisActual (whose instances are
backed by sorryAx); the transitive imports are S1745, S1767 and S1770, all sorry-free.

## Contents

1. Section 1: the category FiniteEtaleAlg K := (CommAlgCat.FiniteEtale.{0} K)^op and the four
   actual fields (instHasTerminal, instHasPullbacks, instHasFiniteCoproducts,
   instHasQuotientsByFiniteGroups), plus the statement that S1767's (G2) hypothesis slot is
   now discharged (hasQuotientsByFiniteGroupsField_holds).
2. Section 2: the remaining field (G3) as an explicit hypothesis, in the exact shape used by
   S1767, together with its class-field shape (instance-implicit Mono) and conversions.
3. Section 3: the assembly preGaloisCategory, and its recovery of the assemblies of S1767
   (with (G2) plugged in) and of S1770 (with the other fields plugged in).
4. Section 4: galoisCategory from (G3) + a fibre functor, and the Galois equivalence
   FiniteEtaleAlg K ~= ContAction FintypeCat (Aut (geometricFiber K)).
5. Section 5: consistency checks (definitional equality of the category with S1745 / S1767 /
   S1770, typeclass search finding the actual instances, the class projections).
6. Section 6: axiom audit: every declaration depends only on propext, Classical.choice and
   Quot.sound; in particular none depends on sorryAx.

## Universe conventions

As in S1767 and S1745, K : Type (universe 0) and the category is
(CommAlgCat.FiniteEtale.{0} K)^op : Type 1 with hom types in Type, i.e. Category.{0, 1}.
This is exactly the universe pair for which PreGaloisCategory's hasQuotientsByFiniteGroups
quantifies over G : Type 0, matching S1770's instance at u = 0.  The fibre functor lands in
FintypeCat.{0}.

## References

* [lenstraGSchemes]: H. W. Lenstra, *Galois theory for schemes*, Def. 3.1, (G1)--(G6).
* Mathlib, Mathlib/CategoryTheory/Galois/Basic.lean, .../Equivalence.lean.
* S1745: tmp/sheaf/xif/paper/S1745FiniteEtaleLimitsActual.lean.
* S1767: tmp/sheaf/xif/paper/S1767FiniteEtaleGaloisNoSorryActual.lean.
* S1770: tmp/sheaf/xif/paper/S1770FiniteEtaleFixedPointsActual.lean.
-/
import tmp.sheaf.xif.paper.S1745FiniteEtaleLimitsActual
import tmp.sheaf.xif.paper.S1767FiniteEtaleGaloisNoSorryActual
import tmp.sheaf.xif.paper.S1770FiniteEtaleFixedPointsActual
import Mathlib.CategoryTheory.Galois.Equivalence
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.SingleObj

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete

namespace S1793GaloisAssembly

/-! ### 1. The category and the four actual fields -/

/-- The opposite of the category of finite etale K-algebras: the Galois category of affine
finite etale K-schemes.  Definitionally the category of S1745, S1767 and S1770 (Section 5). -/
abbrev FiniteEtaleAlg (K : Type) [Field K] : Type 1 := (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ

section

variable {K : Type} [Field K]

/-- (G1) K itself is the terminal object of (FiniteEtale K)^op.  This is S1767's
FiniteEtaleAlg.isTerminal_self, restated at the category of this file. -/
def isTerminal_self : IsTerminal (S1767FiniteEtaleGalois.FiniteEtaleAlg.self K) :=
  S1767FiniteEtaleGalois.FiniteEtaleAlg.isTerminal_self (K := K)

/-- Field 1 of GaloisCategory: (FiniteEtale K)^op has a terminal object.  **Actual**
(S1767, Section 1), no hypothesis. -/
instance instHasTerminal : HasTerminal (FiniteEtaleAlg K) :=
  (isTerminal_self (K := K)).hasTerminal

/-- Field 2 of GaloisCategory: pullbacks, i.e. pushouts (tensor products over the common
vertex) in FiniteEtale K.  **Actual**: S1745's instance, transported by S1767. -/
instance instHasPullbacks : HasPullbacks (FiniteEtaleAlg K) :=
  S1767FiniteEtaleGalois.hasPullbacks_S1745 (K := K)

/-- Field 3 of GaloisCategory: finite coproducts, i.e. finite products (Pi-algebras) in
FiniteEtale K.  **Actual**: S1745's instance, transported by S1767. -/
instance instHasFiniteCoproducts : HasFiniteCoproducts (FiniteEtaleAlg K) :=
  S1767FiniteEtaleGalois.hasFiniteCoproducts_S1745 (K := K)

/-- Field 4 of GaloisCategory (Lenstra (G2)): quotients by finite groups.  **Actual**:
S1770's instance.  For a finite group G acting on a finite etale K-algebra A, the colimit of
the action in (FiniteEtale K)^op is the invariant subalgebra A^G, which is again finite etale
over K (S1770.invariantsIsLimit, S1770.etale_subalgebra). -/
instance instHasQuotientsByFiniteGroups (G : Type) [Group G] [Finite G] :
    HasColimitsOfShape (SingleObj G) (FiniteEtaleAlg K) :=
  S1770.FiniteEtaleAlg.hasQuotientsByFiniteGroups (K := K) G

/-- S1767's (G2) hypothesis slot, **discharged**: the exact Prop that S1767 assumed is now a
theorem (S1770).  This is the statement that the conditional assembly of S1767 needed. -/
theorem hasQuotientsByFiniteGroupsField_holds :
    S1767FiniteEtaleGalois.HasQuotientsByFiniteGroupsField K :=
  fun G _ _ => instHasQuotientsByFiniteGroups (K := K) G

/-! ### 2. The remaining field (G3) as an explicit hypothesis -/

/-- Lenstra (G3), the **only** field that is still a hypothesis: every monomorphism in
(FiniteEtale K)^op induces an isomorphism on a direct summand.

This is exactly S1767's field (S1767FiniteEtaleGalois.MonoInducesIsoOnDirectSummandField),
with an explicit Mono i argument. -/
abbrev MonoInducesIsoOnDirectSummandField (K : Type) [Field K] : Prop :=
  S1767FiniteEtaleGalois.MonoInducesIsoOnDirectSummandField K

/-- (G3) in the binder shape of the class field
PreGaloisCategory.monoInducesIsoOnDirectSummand, where Mono i is instance-implicit.  It is
interderivable with MonoInducesIsoOnDirectSummandField; the conversions below are the honest
proofs. -/
abbrev MonoInducesIsoOnDirectSummandField' (K : Type) [Field K] : Prop :=
  ∀ {X Y : FiniteEtaleAlg K} (i : X ⟶ Y) [Mono i],
    ∃ (Z : FiniteEtaleAlg K) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u))

/-- The class-shaped (G3) implies the S1767-shaped one. -/
theorem monoField_of_monoField' (h : MonoInducesIsoOnDirectSummandField' K) :
    MonoInducesIsoOnDirectSummandField K := by
  intro X Y i hi
  letI : Mono i := hi
  exact h i

/-- The S1767-shaped (G3) implies the class-shaped one. -/
theorem monoField'_of_monoField (h : MonoInducesIsoOnDirectSummandField K) :
    MonoInducesIsoOnDirectSummandField' K := by
  intro X Y i hi
  exact h (X := X) (Y := Y) i hi

/-! ### 3. The pre-Galois category with four actual fields -/

/-- **Main assembly.**  (FiniteEtale K)^op is a pre-Galois category, with

* terminal object: K (S1767, proved),
* pullbacks: S1745 (proved),
* finite coproducts: S1745 (proved),
* quotients by finite groups: S1770 (proved),
* (G3) monoInducesIsoOnDirectSummand: the explicit hypothesis hMono.

No sorry: four fields are actual instances of the three imported files, and the fifth is an
explicit argument. -/
theorem preGaloisCategory (hMono : MonoInducesIsoOnDirectSummandField K) :
    PreGaloisCategory (FiniteEtaleAlg K) where
  hasTerminal := instHasTerminal (K := K)
  hasPullbacks := instHasPullbacks (K := K)
  hasFiniteCoproducts := instHasFiniteCoproducts (K := K)
  hasQuotientsByFiniteGroups := fun G _ _ => instHasQuotientsByFiniteGroups (K := K) G
  monoInducesIsoOnDirectSummand := hMono

/-- The same assembly, from (G3) in the class-field (instance-implicit Mono) shape. -/
theorem preGaloisCategory_of_class (hMono : MonoInducesIsoOnDirectSummandField' K) :
    PreGaloisCategory (FiniteEtaleAlg K) :=
  preGaloisCategory (monoField_of_monoField' hMono)

/-- Consistency with S1767: S1767's conditional assembly, run with its (G2) hypothesis
discharged by hasQuotientsByFiniteGroupsField_holds, gives a pre-Galois category with no
hypothesis other than (G3). -/
theorem preGaloisCategory_via_S1767 (hMono : MonoInducesIsoOnDirectSummandField K) :
    PreGaloisCategory (S1767FiniteEtaleGalois.FiniteEtaleAlg K) :=
  S1767FiniteEtaleGalois.preGaloisCategory (K := K)
    (hasQuotientsByFiniteGroupsField_holds (K := K)) hMono

/-- Consistency with S1770: S1770's assembly preGaloisCategoryOfOtherFields, run with the
terminal object of S1767 and the pullbacks / finite coproducts of S1745, gives the same
pre-Galois category from (G3) alone. -/
theorem preGaloisCategory_via_S1770 (hMono : MonoInducesIsoOnDirectSummandField K) :
    PreGaloisCategory (S1770.FiniteEtaleAlg K) :=
  S1770.preGaloisCategoryOfOtherFields (K := K)
    (instHasTerminal (K := K)) (instHasPullbacks (K := K)) (instHasFiniteCoproducts (K := K))
    (fun {X Y} i hi => hMono (X := X) (Y := Y) i hi)

/-! ### 4. The Galois category from (G3) and a fibre functor -/

/-- The geometric fibre functor S |-> Hom_K(S, Kbar), i.e. S1767's
CommAlgCat.FiniteEtale.fiber K (AlgebraicClosure K): no functor is invented here. -/
abbrev geometricFiber (K : Type) [Field K] : FiniteEtaleAlg K ⥤ FintypeCat.{0} :=
  S1767FiniteEtaleGalois.geometricFiber K

/-- Field 6 of GaloisCategory (Lenstra (G4)--(G6)), at the PreGaloisCategory instance produced
by preGaloisCategory: the geometric fibre functor is a fibre functor.  This is S1767's
FiberFunctorField, i.e. Mathlib's PreGaloisCategory.FiberFunctor (geometricFiber K). -/
abbrev FiberFunctorField (K : Type) [Field K]
    (hPre : PreGaloisCategory (FiniteEtaleAlg K)) : Prop :=
  S1767FiniteEtaleGalois.FiberFunctorField K hPre

/-- **Assembly, step 2.**  (G3) together with a fibre-functor structure on the geometric fibre
functor turns (FiniteEtale K)^op into a Galois category.  The fibre functor of the
GaloisCategory instance is geometricFiber K, fed explicitly, not an arbitrary choice. -/
theorem galoisCategory (hMono : MonoInducesIsoOnDirectSummandField K)
    (hFiber : FiberFunctorField K (preGaloisCategory (K := K) hMono)) :
    GaloisCategory (FiniteEtaleAlg K) := by
  letI : PreGaloisCategory (FiniteEtaleAlg K) := preGaloisCategory hMono
  exact GaloisCategory.mk ⟨geometricFiber K, ⟨hFiber⟩⟩

/-- **Main theorem of Galois theory for finite etale K-algebras**, conditional only on (G3) and
the fibre-functor structure: (FiniteEtale K)^op is equivalent to finite sets with a continuous
action of the automorphism group of the geometric fibre functor.  This is Mathlib's
PreGaloisCategory.functorToContAction, so the functor of the equivalence is geometricFiber K.

The unconditional version (with FiberFunctor also proved) is not available yet; nothing is
postulated here. -/
noncomputable def galoisEquivalence (hMono : MonoInducesIsoOnDirectSummandField K)
    (hFiber : FiberFunctorField K (preGaloisCategory (K := K) hMono)) :
    FiniteEtaleAlg K ≌ ContAction FintypeCat (Aut (geometricFiber K)) := by
  letI : PreGaloisCategory (FiniteEtaleAlg K) := preGaloisCategory hMono
  letI : PreGaloisCategory.FiberFunctor (geometricFiber K) := hFiber
  letI : GaloisCategory (FiniteEtaleAlg K) := galoisCategory hMono hFiber
  exact (PreGaloisCategory.functorToContAction (geometricFiber K)).asEquivalence

/-! ### 5. Consistency checks -/

/-- The category of this file is S1745's category, definitionally. -/
example : (S1745.FiniteEtaleAlg K : Type 1) = (FiniteEtaleAlg K : Type 1) := rfl

/-- The category of this file is S1767's category, definitionally. -/
example : (S1767FiniteEtaleGalois.FiniteEtaleAlg K : Type 1) = (FiniteEtaleAlg K : Type 1) := rfl

/-- The category of this file is S1770's category, definitionally. -/
example : (S1770.FiniteEtaleAlg K : Type 1) = (FiniteEtaleAlg K : Type 1) := rfl

/-- Typeclass search finds the actual terminal object (S1767). -/
example : HasTerminal (FiniteEtaleAlg K) := inferInstance

/-- Typeclass search finds the actual pullback instance (S1745). -/
example : HasPullbacks (FiniteEtaleAlg K) := inferInstance

/-- Typeclass search finds the actual finite coproduct instance (S1745). -/
example : HasFiniteCoproducts (FiniteEtaleAlg K) := inferInstance

/-- Typeclass search finds the actual quotients-by-finite-groups instance (S1770) for an
arbitrary finite group G. -/
example (G : Type) [Group G] [Finite G] :
    HasColimitsOfShape (SingleObj G) (FiniteEtaleAlg K) := inferInstance

/-- S1767's exact (G2) field is proved, not assumed. -/
example : S1767FiniteEtaleGalois.HasQuotientsByFiniteGroupsField K :=
  hasQuotientsByFiniteGroupsField_holds

/-- S1770's own (G2) field, transported to this file's category. -/
example : S1770.HasQuotientsByFiniteGroupsField (K := K) :=
  S1770.hasQuotientsByFiniteGroupsField_holds

/-- **Target check 1.**  PreGaloisCategory at the category written literally as
(CommAlgCat.FiniteEtale K)^op, from (G3) alone. -/
example (hMono : MonoInducesIsoOnDirectSummandField K) :
    PreGaloisCategory ((CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) :=
  preGaloisCategory hMono

/-- **Target check 2.**  GaloisCategory at the same category, from (G3) and a fibre functor. -/
example (hMono : MonoInducesIsoOnDirectSummandField K)
    (hFiber : FiberFunctorField K (preGaloisCategory (K := K) hMono)) :
    GaloisCategory ((CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) :=
  galoisCategory hMono hFiber

/-- The (G3) field of the assembled PreGaloisCategory is the hypothesis itself (the other four
fields are the actual instances, see preGaloisCategory). -/
example (hMono : MonoInducesIsoOnDirectSummandField K) {X Y : FiniteEtaleAlg K} (i : X ⟶ Y)
    [Mono i] :
    ∃ (Z : FiniteEtaleAlg K) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u)) :=
  @PreGaloisCategory.monoInducesIsoOnDirectSummand (FiniteEtaleAlg K) _
    (preGaloisCategory hMono) X Y i _

/-- The (G2) field of the assembled PreGaloisCategory, through the class projection: it is
S1770's actual instance. -/
example (hMono : MonoInducesIsoOnDirectSummandField K) (G : Type) [Group G] [Finite G] :
    HasColimitsOfShape (SingleObj G) (FiniteEtaleAlg K) :=
  @PreGaloisCategory.hasQuotientsByFiniteGroups (FiniteEtaleAlg K) _
    (preGaloisCategory hMono) G _ _

/-! ### 6. Axiom audit

Every declaration below depends only on propext, Classical.choice and Quot.sound; in
particular none depends on sorryAx, and the (G3) hypothesis is a free variable, not an axiom.
The S1745 and S1770 instances audited here are the ones used by the assembly. -/

#print axioms S1745.FiniteEtaleClosure.hasPullbacks
#print axioms S1745.FiniteEtaleClosure.hasFiniteCoproducts
#print axioms S1770.FiniteEtaleAlg.hasQuotientsByFiniteGroups
#print axioms S1767FiniteEtaleGalois.FiniteEtaleAlg.isTerminal_self

#print axioms S1793GaloisAssembly.instHasTerminal
#print axioms S1793GaloisAssembly.instHasPullbacks
#print axioms S1793GaloisAssembly.instHasFiniteCoproducts
#print axioms S1793GaloisAssembly.instHasQuotientsByFiniteGroups
#print axioms S1793GaloisAssembly.hasQuotientsByFiniteGroupsField_holds
#print axioms S1793GaloisAssembly.preGaloisCategory
#print axioms S1793GaloisAssembly.preGaloisCategory_of_class
#print axioms S1793GaloisAssembly.preGaloisCategory_via_S1767
#print axioms S1793GaloisAssembly.preGaloisCategory_via_S1770
#print axioms S1793GaloisAssembly.galoisCategory
#print axioms S1793GaloisAssembly.galoisEquivalence

end

end S1793GaloisAssembly
