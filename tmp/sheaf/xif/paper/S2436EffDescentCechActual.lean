import tmp.sheaf.xif.paper.S2134D9DescentActual
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.ZMod.Basic

/-!
# S2436: the Cech/descent comparison for the D9 effective-descent half

This file works on the effective-descent half of the D9 stack target, i.e. on

  S2134EffDescentOnEtaleFamilies K

for the slice-sheaf prestack

  S2029SheafPrestack K = (etaleTopology K).pseudofunctorOver (Type u)

on the etale site of schemes over a field (S2134, S2093, S2029).

## What is proved here (unconditional, no sorry, no new axiom)

1. The Cech/stack form of the target.  The D9 stack target is equivalent to the
   Mathlib-native stack condition IsStackFor on the actual etale precoverage covers,
   and that comparison is in turn exactly "prestack half + effective descent".  The
   precise equivalences are
   S2093SheafStackOnEtaleFamilies_iff_prestack_and_effDescent and
   S2093LargeSheafStackMissing_iff_prestack_and_amalgam.
2. The exact missing theorem, in general form.  The construction which is absent
   in Mathlib is the "stack of sheaves" theorem for J.pseudofunctorOver (Type u)
   on an arbitrary site: every descent datum for the slice-sheaf pseudofunctor on a
   covering family has an amalgamation.  This is isolated as the Props
   S2436SheafStackTheorem, S2436SheafEffDescentTheorem and
   S2436SheafAmalgamationTheorem; the concrete D9 instance is
   S2436D9Amalgamation K.
3. The general theorem implies the D9 target (actual lemmas), so the D9
   effective-descent half is exactly the specialization of the general
   stack-of-sheaves theorem to the etale site of SchemeOverField K.
4. A counterexample showing that the base cases do not extend.  For the Yoneda
   pseudofunctor U |-> Discrete (U -> ZMod 2) on AddCommGrpCat and the non-split
   monomorphism Int.castAddHom Q : Z -> Q, the canonical descent datum given by the
   quotient map Z -> ZMod 2 has no amalgamation.  Hence the schema "every singleton
   family has effective descent" is false, and the identity/split-epi proofs of S2134
   cannot be generalized by the same argument.

## Honest boundary

No general effective-descent statement is proved.  Mathlib v4.32.2 contains no
instance of Pseudofunctor.IsStack at all and no "stack of sheaves" theorem; the only
constructors are IsStack.of_isStackFor / IsStack.of_precoverage, which take the stack
condition as an input.  The exact first missing theorem signature is stated below as
a Prop; no inhabitant is asserted.
-/

noncomputable section
open CategoryTheory
open scoped Bicategory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2436EffDescentCechActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2093D9StackActual
open LeanFormal.IUT.XiFPaper.S2029GiraudStackificationActual
open LeanFormal.IUT.XiFPaper.S2134D9DescentActual

universe v u v' u'

/-! ## 1. The Cech/stack comparison form of the D9 target -/

section Field

variable {K : Type u} [Field K]

/-- **The Cech/stack comparison form.**  The target S2134EffDescentOnEtaleFamilies
is the effective-descent (essential-surjectivity) half of the Mathlib-native stack
condition IsStackFor on the actual etale precoverage covers.  Conversely, the
prestack half together with effective descent gives the full IsStackFor.

This is the precise sense in which the D9 effective-descent half is a Cech/descent
comparison statement: IsStackFor R says that the Cech descent functor toDescentData
for the family of all arrows of R is an equivalence of categories. -/
theorem S2093SheafStackOnEtaleFamilies_iff_prestack_and_effDescent :
    S2093SheafStackOnEtaleFamilies (K := K) ↔
      S2093SheafPrestack (K := K) ∧ S2134EffDescentOnEtaleFamilies (K := K) := by
  constructor
  · intro h
    haveI hP : (S2029SheafPrestack K).IsPrestack
        (Iut.SchemeOverField.etaleTopology K) := by
      rw [← S2093EtalePrecoverage_toGrothendieck (K := K)]
      refine Pseudofunctor.IsPrestack.of_precoverage
        (F := S2029SheafPrestack K) (J := S2093EtalePrecoverage K) ?_
      intro S R hR
      exact (h S R hR).isPrestackFor
    exact ⟨hP, fun S R hR => (h S R hR).essSurj⟩
  · rintro ⟨hP, hE⟩ S R hR
    haveI : (S2029SheafPrestack K).IsPrestack
        (Iut.SchemeOverField.etaleTopology K) := hP
    have hJ : Sieve.ofArrows _
        (fun (g : R.category) => g.obj.hom) ∈
          Iut.SchemeOverField.etaleTopology K S := by
      rw [Sieve.ofArrows_category', ← S2093EtalePrecoverage_toGrothendieck (K := K)]
      exact Precoverage.generate_mem_toGrothendieck hR
    have hff := (S2029SheafPrestack K).fullyFaithfulToDescentData
      (fun (g : R.category) => g.obj.hom) hJ
    exact ⟨{ faithful := hff.faithful
             full := hff.full
             essSurj := hE S R hR }⟩

/-- **The amalgamation form of the D9 effective-descent half.**  Every descent datum
for an actual etale precoverage cover has an amalgamation: an object of the fibre at
the base together with an isomorphism of its descent data to the given datum.  This is
the concrete construction which the general stack-of-sheaves theorem supplies. -/
noncomputable def S2436D9Amalgamation (K : Type u) [Field K] : Prop :=
  ∀ (S : Iut.SchemeOverField K) (R : Presieve S),
    R ∈ (S2093EtalePrecoverage K).coverings S →
      ∀ D : (S2029SheafPrestack K).DescentData
          (fun (g : R.category) => g.obj.hom),
        Nonempty (Amalgam (S2029SheafPrestack K)
          (fun (g : R.category) => g.obj.hom) D)

/-- The amalgamation form is exactly the effective-descent form. -/
theorem S2436D9Amalgamation_iff :
    S2436D9Amalgamation (K := K) ↔
      S2134EffDescentOnEtaleFamilies (K := K) := by
  rw [S2134EffDescentOnEtaleFamilies_iff_amalgam]
  rfl

/-- **The D9 stack target as prestack half plus amalgamation.**  This is the precise
Cech/descent comparison reduction of the D9 target: it is not an IsStack assertion,
but the conjunction of the descent-of-morphisms half (S2103) and the existence of
amalgamations for all actual etale covering families. -/
theorem S2093LargeSheafStackMissing_iff_prestack_and_amalgam :
    S2093LargeSheafStackMissing (K := K) ↔
      S2093SheafPrestack (K := K) ∧ S2436D9Amalgamation (K := K) := by
  rw [S2093LargeSheafStackMissing_iff_halves (K := K),
    S2436D9Amalgamation_iff (K := K)]

/-- The same in Mathlib's native IsStackFor vocabulary. -/
theorem S2093LargeSheafStackMissing_iff_cechComparison :
    S2093LargeSheafStackMissing (K := K) ↔
      S2093SheafStackOnEtaleFamilies (K := K) :=
  S2093SheafStackOnEtaleFamilies_iff (K := K)

end Field

/-! ## 2. The exact missing theorem, in general form

Mathlib has the pseudofunctor J.pseudofunctorOver A (the slice sheaves on the site),
but it has no theorem that it is a stack.  We record the exact theorem which is
missing, first for the full stack condition, then for its effective-descent half,
and finally in the amalgamation form.  The D9 target is the specialization of the
effective-descent half to the etale site of SchemeOverField K. -/

/-- **The exact missing theorem: the stack of sheaves.**  For every Grothendieck
topology J on a category C, the pseudofunctor X |-> Sheaf (J.over X) (Type u) is a
stack for J.

Mathlib v4.32.2 does not contain this theorem (nor any IsStack instance at all).
The theorem includes both the prestack half and effective descent; the
effective-descent half alone is S2436SheafEffDescentTheorem below. -/
def S2436SheafStackTheorem : Prop :=
  ∀ {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C),
    (J.pseudofunctorOver (Type u)).IsStack J

/-- **The exact missing effective-descent theorem.**  For every covering presieve
R of an object S, the Cech descent functor of the slice-sheaf pseudofunctor is
essentially surjective: every descent datum is isomorphic to the descent data of an
actual slice sheaf.  This is the effective-descent half of S2436SheafStackTheorem,
stated without the prestack half. -/
def S2436SheafEffDescentTheorem : Prop :=
  ∀ {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (S : C) (R : Presieve S), Sieve.generate R ∈ J S →
      HasEffectiveDescentPresieve (J.pseudofunctorOver (Type u)) R

/-- **The exact missing construction, in amalgamation form.**  Every descent datum
on a covering presieve for the slice-sheaf pseudofunctor has an amalgamation in the
slice-sheaf category over the base.  This is the literal construction which the
stack-of-sheaves theorem supplies and which Mathlib does not contain. -/
def S2436SheafAmalgamationTheorem : Prop :=
  ∀ {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (S : C) (R : Presieve S), Sieve.generate R ∈ J S →
      ∀ D : (J.pseudofunctorOver (Type u)).DescentData
          (fun (g : R.category) => g.obj.hom),
        Nonempty (Amalgam (J.pseudofunctorOver (Type u))
          (fun (g : R.category) => g.obj.hom) D)

/-- A stack is in particular effective descent on every covering presieve. -/
theorem S2436SheafEffDescentTheorem_of_stack
    (h : S2436SheafStackTheorem) :
    S2436SheafEffDescentTheorem := by
  intro C _ J S R hR
  haveI : (J.pseudofunctorOver (Type u)).IsStack J := h J
  exact (Pseudofunctor.isStackFor (F := J.pseudofunctorOver (Type u)) R hR).essSurj

/-- Amalgamation and essential surjectivity of the Cech descent functor are
equivalent, uniformly in the site and the cover. -/
theorem S2436SheafAmalgamationTheorem_iff :
    S2436SheafAmalgamationTheorem ↔
      S2436SheafEffDescentTheorem := by
  constructor
  · intro h C _ J S R hR
    exact (hasEffectiveDescent_iff_amalgam
      (F := J.pseudofunctorOver (Type u))
      (f := fun (g : R.category) => g.obj.hom)).mpr
      (fun D => h (J := J) (S := S) (R := R) hR D)
  · intro h C _ J S R hR D
    exact (hasEffectiveDescent_iff_amalgam
      (F := J.pseudofunctorOver (Type u))
      (f := fun (g : R.category) => g.obj.hom)).mp
      (h (J := J) (S := S) (R := R) hR) D

section D9Specialization

variable {K : Type u} [Field K]

/-- **The D9 target is a specialization of the general effective-descent theorem.**
This is the precise reduction of S2134EffDescentOnEtaleFamilies to the general
stack-of-sheaves / Cech-amalgamation theorem: the D9 statement is just the case
C = SchemeOverField K, J = etaleTopology K, A = Type u of the general
effective-descent half. -/
theorem S2134EffDescentOnEtaleFamilies_of_general
    (h : S2436SheafEffDescentTheorem) :
    S2134EffDescentOnEtaleFamilies (K := K) := by
  intro S R hR
  have hJ : Sieve.generate R ∈
      Iut.SchemeOverField.etaleTopology K S := by
    rw [← S2093EtalePrecoverage_toGrothendieck (K := K)]
    exact Precoverage.generate_mem_toGrothendieck hR
  have h' := h (J := Iut.SchemeOverField.etaleTopology K) (S := S) (R := R) hJ
  simpa [S2029SheafPrestack] using h'

/-- The D9 amalgamation form is a specialization of the general amalgamation
theorem. -/
theorem S2436D9Amalgamation_of_general
    (h : S2436SheafAmalgamationTheorem) :
    S2436D9Amalgamation (K := K) := by
  intro S R hR D
  have hJ : Sieve.generate R ∈
      Iut.SchemeOverField.etaleTopology K S := by
    rw [← S2093EtalePrecoverage_toGrothendieck (K := K)]
    exact Precoverage.generate_mem_toGrothendieck hR
  exact h (J := Iut.SchemeOverField.etaleTopology K) (S := S) (R := R) hJ D

end D9Specialization

/-! ## 3. The general theorem implies the full D9 stack target -/

section GeneralToD9

variable {K : Type u} [Field K]

/-- **The general stack-of-sheaves theorem proves the D9 stack target.**  This is
the strongest form of the reduction: the single general theorem
S2436SheafStackTheorem, specialized to the etale site of SchemeOverField K, is
exactly S2093LargeSheafStackMissing. -/
theorem S2093LargeSheafStackMissing_of_general
    (h : S2436SheafStackTheorem) :
    S2093LargeSheafStackMissing (K := K) := by
  have h' := h (J := Iut.SchemeOverField.etaleTopology K)
  simpa [S2093LargeSheafStackMissing, S2029SheafPrestack] using h'

/-- The general effective-descent theorem gives the named D9 first missing. -/
theorem S2134FirstMissing_of_general
    (h : S2436SheafEffDescentTheorem) :
    S2134FirstMissing (K := K) := by
  simpa [S2134FirstMissing] using
    S2134EffDescentOnEtaleFamilies_of_general (K := K) h

end GeneralToD9

/-! ## 4. Why the base cases do not extend: a counterexample

The base cases of S2134 are the identity cover, every presieve whose generated sieve
is maximal, and every cover containing a split epimorphism.  The proof in those cases
reads the glued object off the index of the identity (or of a splitting), using the
pseudofunctor unit F.mapId.

The following counterexample shows that the underlying schema "every singleton
family has effective descent" is false for a general pseudofunctor.  Take

* C = AddCommGrpCat;
* F = the Yoneda pseudofunctor U |-> Discrete (U ⟶ ZMod 2);
* f : Z -> Q the inclusion of the integers into the rationals (a monomorphism);
* m : Z -> ZMod 2 the reduction modulo 2.

Since Hom(Q, ZMod 2) is trivial (Q is divisible and every element of ZMod 2 is
2-torsion), every descent datum on the singleton family {f} with object m exists
formally; but an amalgamation would be a group hom Q -> ZMod 2 whose composite with f
is m, which is impossible because every such hom is zero and m is not.  Thus the
family has a descent datum with no amalgamation.

The map f is not a split epimorphism: a section s : Q -> Z would give, at 1/2,
an integer s(1/2) with 2 * s(1/2) = 1, which is impossible.  Hence neither the
split-epi base case nor (because 1_Q does not factor through f) the maximal-sieve
base case applies. -/

namespace Counterexample

/-- The source of the counterexample map, the integers as an additive group. -/
abbrev counterX : AddCommGrpCat.{0} := AddCommGrpCat.of ℤ

/-- The target of the counterexample map, the rationals as an additive group. -/
abbrev counterS : AddCommGrpCat.{0} := AddCommGrpCat.of ℚ

/-- The coefficient group of the Yoneda pseudofunctor. -/
abbrev counterT : AddCommGrpCat.{0} := AddCommGrpCat.of (ZMod 2)

/-- The inclusion of the integers into the rationals. -/
noncomputable def counterF : counterX ⟶ counterS :=
  AddCommGrpCat.ofHom (Int.castAddHom ℚ)

/-- The reduction modulo 2. -/
noncomputable def counterM : counterX ⟶ counterT :=
  AddCommGrpCat.ofHom (Int.castAddHom (ZMod 2))

/-- The inclusion of the integers into the rationals is a monomorphism. -/
instance : Mono counterF := by
  constructor
  intro Z g₁ g₂ h
  rw [← AddCommGrpCat.ofHom_hom g₁, ← AddCommGrpCat.ofHom_hom g₂]
  congr 1
  apply AddMonoidHom.ext
  intro x
  have hx := congrFun (congrArg (fun (k : Z ⟶ counterS) => (k : Z → ℚ)) h) x
  simp only [ConcreteCategory.comp_apply] at hx
  exact Int.cast_injective hx

/-- Every element of ZMod 2 is 2-torsion. -/
lemma zmod_two_add_self (z : ZMod 2) : z + z = 0 := by
  fin_cases z <;> decide

/-- The group of homomorphisms Q -> ZMod 2 is trivial: Q is divisible by 2, while
ZMod 2 is 2-torsion. -/
lemma hom_rat_zmod_two (M : counterS ⟶ counterT) :
    M = AddCommGrpCat.ofHom 0 := by
  rw [← AddCommGrpCat.ofHom_hom M,
    ← AddCommGrpCat.ofHom_hom (AddCommGrpCat.ofHom 0 : counterS ⟶ counterT)]
  congr 1
  apply AddMonoidHom.ext
  intro q
  have hq : q = (2 : ℕ) • (q / 2) := by
    rw [nsmul_eq_mul]
    ring
  calc
    (AddCommGrpCat.Hom.hom M) q
        = (AddCommGrpCat.Hom.hom M) ((2 : ℕ) • (q / 2)) := congrArg _ hq
    _ = (2 : ℕ) • (AddCommGrpCat.Hom.hom M) (q / 2) := map_nsmul _ 2 _
    _ = 0 := by
          rw [two_nsmul]
          exact zmod_two_add_self _
    _ = (AddCommGrpCat.Hom.hom (AddCommGrpCat.ofHom 0 : counterS ⟶ counterT)) q := by
          simp

/-- The reduction modulo 2 is not the zero map. -/
lemma counterM_ne_zero : counterM ≠ AddCommGrpCat.ofHom 0 := by
  intro hm
  have hval := congrArg (fun (k : counterX ⟶ counterT) => (k : ℤ → ZMod 2) 1) hm
  simp [counterM] at hval

/-- The Yoneda pseudofunctor at ZMod 2, as an ordinary functor into Cat. -/
noncomputable def counterYoneda : (AddCommGrpCat.{0})ᵒᵖ ⥤ Cat.{0,0} where
  obj U := Cat.of (Discrete (U.unop ⟶ counterT))
  map {U V} g :=
    (Discrete.functor (fun h : U.unop ⟶ counterT =>
      Discrete.mk (g.unop ≫ h))).toCatHom
  map_id U := by
    apply Cat.Hom.ext
    apply Discrete.functor_ext
    intro i
    rfl
  map_comp {U V W} f g := by
    apply Cat.Hom.ext
    apply Discrete.functor_ext
    intro i
    simp [Category.assoc]

/-- The counterexample pseudofunctor. -/
noncomputable def counterPrestack :
    Pseudofunctor (LocallyDiscrete (AddCommGrpCat.{0})ᵒᵖ) Cat.{0,0} :=
  counterYoneda.toPseudofunctor'

/-- The descent datum on the singleton family (counterF) given by the reduction
modulo 2.  Since counterF is a monomorphism, all the compatibility isomorphisms are
forced. -/
noncomputable def counterDatum :
    counterPrestack.DescentData (fun _ : Unit => counterF) where
  obj _ := Discrete.mk counterM
  hom := by
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    obtain rfl : i₁ = () := Subsingleton.elim i₁ ()
    obtain rfl : i₂ = () := Subsingleton.elim i₂ ()
    have h : f₁ = f₂ := (cancel_mono counterF).mp (by rw [hf₁, hf₂])
    subst h
    exact 𝟙 _
  pullHom_hom := by
    intro Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
    obtain rfl : i₁ = () := Subsingleton.elim i₁ ()
    obtain rfl : i₂ = () := Subsingleton.elim i₂ ()
    haveI : Subsingleton
        ((counterPrestack.map gf₁.op.toLoc).toFunctor.obj (Discrete.mk counterM) ⟶
          (counterPrestack.map gf₂.op.toLoc).toFunctor.obj (Discrete.mk counterM)) :=
      Discrete.instSubsingletonDiscreteHom _ _
    exact Subsingleton.elim _ _
  hom_self := by
    intro Y q i g hg
    obtain rfl : i = () := Subsingleton.elim i ()
    haveI : Subsingleton
        ((counterPrestack.map g.op.toLoc).toFunctor.obj (Discrete.mk counterM) ⟶
          (counterPrestack.map g.op.toLoc).toFunctor.obj (Discrete.mk counterM)) :=
      Discrete.instSubsingletonDiscreteHom _ _
    exact Subsingleton.elim _ _
  hom_comp := by
    intro Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
    obtain rfl : i₁ = () := Subsingleton.elim i₁ ()
    obtain rfl : i₂ = () := Subsingleton.elim i₂ ()
    obtain rfl : i₃ = () := Subsingleton.elim i₃ ()
    haveI : Subsingleton
        ((counterPrestack.map f₁.op.toLoc).toFunctor.obj (Discrete.mk counterM) ⟶
          (counterPrestack.map f₃.op.toLoc).toFunctor.obj (Discrete.mk counterM)) :=
      Discrete.instSubsingletonDiscreteHom _ _
    exact Subsingleton.elim _ _

/-- **The counterexample.**  The descent datum counterDatum has no amalgamation for the
singleton family (counterF).  Consequently the singleton family does not have effective
descent, although it consists of a monomorphism and the ambient pseudofunctor is an
honest (Yoneda) pseudofunctor. -/
theorem counterexample_not_effectiveDescent :
    ¬ HasEffectiveDescent counterPrestack (fun _ : Unit => counterF) := by
  intro h
  obtain ⟨M, ⟨e⟩⟩ := h.mem_essImage counterDatum
  rcases M with ⟨M'⟩
  have h2 : counterF ≫ M' = counterM := by
    have hmor : (Discrete.mk (counterF ≫ M') : Discrete (counterX ⟶ counterT)) ⟶
        (Discrete.mk counterM : Discrete (counterX ⟶ counterT)) :=
      e.hom.hom ()
    obtain ⟨⟨heq⟩⟩ := hmor
    simpa using heq
  have hzero : counterF ≫ (AddCommGrpCat.ofHom (0 : ℚ →+ ZMod 2)) =
      AddCommGrpCat.ofHom (0 : ℤ →+ ZMod 2) := by
    change AddCommGrpCat.ofHom (Int.castAddHom ℚ) ≫
        AddCommGrpCat.ofHom (0 : ℚ →+ ZMod 2) = _
    rw [← AddCommGrpCat.ofHom_comp]
    simp
  have hM : M' = AddCommGrpCat.ofHom (0 : ℚ →+ ZMod 2) := hom_rat_zmod_two M'
  have h3 : counterF ≫ M' = AddCommGrpCat.ofHom (0 : ℤ →+ ZMod 2) := by
    rw [hM]
    exact hzero
  have : counterM = AddCommGrpCat.ofHom (0 : ℤ →+ ZMod 2) := by
    rw [← h2, h3]
  exact counterM_ne_zero this

/-- **The base-case schema fails.**  There is a genuine pseudofunctor and a singleton
family for which effective descent fails.  This is the formal statement that the
identity-cover and split-epimorphism base cases of S2134 do not extend to arbitrary
families by the same argument. -/
theorem baseCaseSchema_fails :
    ∃ (C : Type 1) (_ : Category C)
      (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{0,0})
      (X S : C) (f : X ⟶ S),
        ¬ HasEffectiveDescent F (fun _ : Unit => f) :=
  ⟨AddCommGrpCat.{0},
    (inferInstance : Category.{0, 1} (AddCommGrpCat.{0})),
    counterPrestack, counterX, counterS,
    counterF, counterexample_not_effectiveDescent⟩

end Counterexample

/-! ## 5. Interface checks and axiom footprint -/

#check @S2093SheafStackOnEtaleFamilies_iff_prestack_and_effDescent
#check @S2436D9Amalgamation
#check @S2436D9Amalgamation_iff
#check @S2093LargeSheafStackMissing_iff_prestack_and_amalgam
#check @S2093LargeSheafStackMissing_iff_cechComparison
#check @S2436SheafStackTheorem
#check @S2436SheafEffDescentTheorem
#check @S2436SheafAmalgamationTheorem
#check @S2436SheafEffDescentTheorem_of_stack
#check @S2436SheafAmalgamationTheorem_iff
#check @S2134EffDescentOnEtaleFamilies_of_general
#check @S2436D9Amalgamation_of_general
#check @S2093LargeSheafStackMissing_of_general
#check @S2134FirstMissing_of_general
#check @Counterexample.counterexample_not_effectiveDescent
#check @Counterexample.baseCaseSchema_fails

#print axioms S2093SheafStackOnEtaleFamilies_iff_prestack_and_effDescent
#print axioms S2436D9Amalgamation_iff
#print axioms S2093LargeSheafStackMissing_iff_prestack_and_amalgam
#print axioms S2093LargeSheafStackMissing_iff_cechComparison
#print axioms S2436SheafEffDescentTheorem_of_stack
#print axioms S2436SheafAmalgamationTheorem_iff
#print axioms S2134EffDescentOnEtaleFamilies_of_general
#print axioms S2436D9Amalgamation_of_general
#print axioms S2093LargeSheafStackMissing_of_general
#print axioms S2134FirstMissing_of_general
#print axioms Counterexample.counterexample_not_effectiveDescent
#print axioms Counterexample.baseCaseSchema_fails

end LeanFormal.IUT.XiFPaper.S2436EffDescentCechActual
