/-
# S2440: the general amalgamation / stack-of-slice-sheaves theorem

## The target and the exact mathematical content

S2439 records the D9 effective-descent first missing in the amalgamation form
`S2439AmalgamationInterface K`: for every test object `S : SchemeOverField K`, every
presieve `R` from the actual etale precoverage `S2093EtalePrecoverage K` and every
descent datum `D` for the slice-sheaf prestack `S2029SheafPrestack K`, an amalgamation
exists.  Equivalently (S2134/S2439) the descent functor of the prestack is essentially
surjective on every actual etale covering family.

This file determines exactly what that statement is, proves every reduction that is
available without new input, and isolates the exact missing theorem.

* The prestack `S2029SheafPrestack K` is, by definition,
  `(SchemeOverField.etaleTopology K).pseudofunctorOver (Type u)`: the pseudofunctor
  `U |-> Sheaf ((etaleTopology K).over U) (Type u)` of sheaves on the slice sites.
  Its effective descent for a covering family is exactly the statement that *sheaves on
  slice sites form a stack*, i.e. Cech descent for the slice topos.  This is a standard
  theorem (SGA 4, Giraud, Laumon--Moret-Bailly 3.2); it is **not** in Mathlib v4.32.2.
  Mathlib contains the *definitions* of `Pseudofunctor.IsPrestack` and
  `Pseudofunctor.IsStack`, the descent-data category, and the constructor
  `IsStack.of_isStackFor`, but no instance of `IsStack` for any category-valued
  pseudofunctor at all, in particular none for `J.pseudofunctorOver A`.

* We state the missing theorem for an arbitrary site in full generality
  (`S2440SliceSheafStackAll`, `S2440SliceSheafEffectiveDescentAll`,
  `S2440SliceSheafAmalgamationAll`), prove that these forms are equivalent
  (`S2440SliceSheafStackAll_iff`, `S2440SliceSheafEffectiveDescentAll_iff_amalgamation`),
  and instantiate them at the D9 site to deduce the target
  (`S2440ExactMissing_to_target`, `S2440ExactMissing_to_interface`).

* Conversely, we prove that the target together with the prestack half
  `S2093SheafPrestack K` (the S2103 input) is *exactly* the etale-site instance of the
  missing theorem, with no loss (`S2440EtaleSliceStack_iff`,
  `S2440EtaleSliceEffectiveDescent_of_target_and_prestack`).

* We prove the actual non-vacuous base cases at the general level: effective descent
  for every family whose generated sieve is maximal (this contains the identity cover
  and every cover containing a split epimorphism), and for the empty family when the
  fibre is nonempty.  Consequently the missing theorem is *exactly* the statement for
  proper generated sieves (`S2440SliceEffectiveDescent_iff_proper`,
  `S2440SliceAmalgamation_iff_proper`).

## Honest boundary

No `sorry`, no `axiom`, no `True`/`PUnit`/`ULift` carrier, no fabricated `IsStack`
instance and no new hypothesis in any theorem about the target.  The missing theorem is
a named `Prop` with *no inhabitant* asserted.  The only axioms used are `propext`,
`Classical.choice` and `Quot.sound`.
-/

import tmp.sheaf.xif.paper.S2439D9ProofActual

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2093D9StackActual
open LeanFormal.IUT.XiFPaper.S2029GiraudStackificationActual
open LeanFormal.IUT.XiFPaper.S2103D9PrestackActual
open LeanFormal.IUT.XiFPaper.S2134D9DescentActual
open LeanFormal.IUT.XiFPaper.S2439D9ProofActual

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2440AmalgamationActual

universe v u v' u' w

/-! ## 1. The general site-level interface: sheaves on slices as a stack -/

section General

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v'} A]

/-- **The stack of sheaves on slices, at a fixed site and target category.**  The
pseudofunctor `X |-> Sheaf (J.over X) A` is a stack for `J`.

This is the theorem that Mathlib v4.32.2 does not have: there is no `IsStack`
instance for any category-valued pseudofunctor in Mathlib, and in particular no
"stack of sheaves" theorem.  The statement is the standard descent theorem for the
slice topos (SGA 4; Giraud, *Cohomologie non abelienne*, II 1.2; Laumon--Moret-Bailly,
*Champs algebriques*, 3.2). -/
def S2440SliceStack : Prop :=
  (J.pseudofunctorOver A).IsStack J

/-- The prestack half at a fixed site: descent of morphisms for
`X |-> Sheaf (J.over X) A`.  In the D9 case this is the S2103 naturality input
(see S2103D9PrestackActual); it is *not* used as a hypothesis anywhere below unless
explicitly stated. -/
def S2440SlicePrestack : Prop :=
  (J.pseudofunctorOver A).IsPrestack J

/-- **The effective-descent half at a fixed site** (the actual missing content of the
D9 target, in general form): for every presieve whose generated sieve is covering,
the descent functor of `J.pseudofunctorOver A` is essentially surjective. -/
def S2440SliceEffectiveDescent : Prop :=
  ∀ (S : C) (R : Presieve S), Sieve.generate R ∈ J S →
    HasEffectiveDescentPresieve (J.pseudofunctorOver A) R

/-- **The amalgamation form at a fixed site**: every descent datum for every covering
family of the slice-sheaf prestack has an actual amalgamation.  This is the precise
construction which is missing. -/
def S2440SliceAmalgamation : Prop :=
  ∀ (S : C) (R : Presieve S), Sieve.generate R ∈ J S →
    ∀ D : (J.pseudofunctorOver A).DescentData (fun (g : R.category) => g.obj.hom),
      Nonempty (Amalgam (J.pseudofunctorOver A) (fun (g : R.category) => g.obj.hom) D)

/-- **Effective descent = existence of amalgamations**, at a fixed site. -/
theorem S2440SliceEffectiveDescent_iff_amalgamation :
    S2440SliceEffectiveDescent J A ↔ S2440SliceAmalgamation J A := by
  unfold S2440SliceEffectiveDescent S2440SliceAmalgamation HasEffectiveDescentPresieve
  refine forall_congr' (fun S => forall_congr' (fun R => imp_congr_right (fun hR => ?_)))
  exact hasEffectiveDescent_iff_amalgam (J.pseudofunctorOver A)
    (fun (g : R.category) => g.obj.hom)

/-- **Exact decomposition of the stack condition at a fixed site.**  The stack-of-slice-
sheaves theorem is precisely the conjunction of the prestack half and the
effective-descent half. -/
theorem S2440SliceStack_iff :
    S2440SliceStack J A ↔ S2440SlicePrestack J A ∧ S2440SliceEffectiveDescent J A := by
  constructor
  · intro h
    refine ⟨h.toIsPrestack, ?_⟩
    intro S R hR
    haveI : (J.pseudofunctorOver A).IsStack J := h
    exact (Pseudofunctor.isStackFor (F := J.pseudofunctorOver A) R hR).essSurj
  · rintro ⟨hP, hE⟩
    haveI : (J.pseudofunctorOver A).IsPrestack J := hP
    refine Pseudofunctor.IsStack.of_isStackFor (F := J.pseudofunctorOver A) ?_
    intro S R hR
    rw [Pseudofunctor.isStackFor_iff]
    have hff := Pseudofunctor.fullyFaithfulToDescentData
      (F := J.pseudofunctorOver A) (f := fun (g : R.arrows.category) => g.obj.hom)
      (J := J) (by rw [Sieve.ofArrows_category', Sieve.generate_sieve]; exact hR)
    exact
      { faithful := hff.faithful
        full := hff.full
        essSurj := hE S R.arrows (by rwa [Sieve.generate_sieve]) }

/-- The amalgamation form of the decomposition. -/
theorem S2440SliceStack_iff_amalgamation :
    S2440SliceStack J A ↔ S2440SlicePrestack J A ∧ S2440SliceAmalgamation J A := by
  rw [S2440SliceStack_iff, S2440SliceEffectiveDescent_iff_amalgamation]

/-! ### 1a. Base cases: maximal generated sieve, empty family, proper reduction -/

/-- **Base case: every family whose generated sieve is maximal has effective descent.**
No hypothesis on `A` and no prestack condition is used.  This covers the identity
cover and every cover containing a split epimorphism. -/
theorem S2440SliceEffectiveDescent_of_generate_top (S : C) (R : Presieve S)
    (hR : Sieve.generate R = ⊤) :
    HasEffectiveDescentPresieve (J.pseudofunctorOver A) R :=
  hasEffectiveDescentPresieve_of_generate_top (J.pseudofunctorOver A) R hR

/-- The amalgamation form of the maximal-sieve base case. -/
theorem S2440SliceAmalgamation_of_generate_top (S : C) (R : Presieve S)
    (hR : Sieve.generate R = ⊤) :
    ∀ D : (J.pseudofunctorOver A).DescentData (fun (g : R.category) => g.obj.hom),
      Nonempty (Amalgam (J.pseudofunctorOver A) (fun (g : R.category) => g.obj.hom) D) := by
  intro D
  exact (hasEffectiveDescent_iff_amalgam (J.pseudofunctorOver A)
    (fun (g : R.category) => g.obj.hom)).mp
    (S2440SliceEffectiveDescent_of_generate_top J A S R hR) D

/-- **Base case: the empty family.**  If the fibre at the base is nonempty then every
descent datum for the empty family has an amalgamation: the empty descent-data category
is a subsingleton category, so any object of the fibre works. -/
theorem S2440SliceAmalgamation_bot {S : C}
    (hM : Nonempty ((J.pseudofunctorOver A).obj (LocallyDiscrete.mk (op S)))) :
    ∀ D : (J.pseudofunctorOver A).DescentData
        (fun (g : (⊥ : Presieve S).category) => g.obj.hom),
      Nonempty (Amalgam (J.pseudofunctorOver A)
        (fun (g : (⊥ : Presieve S).category) => g.obj.hom) D) := by
  intro D
  obtain ⟨M⟩ := hM
  haveI hι : IsEmpty (⊥ : Presieve S).category := ⟨fun x => x.property⟩
  refine ⟨M, Pseudofunctor.DescentData.isoMk (fun i => (hι.false i).elim) ?_⟩
  intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
  exact (hι.false i₁).elim

/-- **The missing theorem is exactly the statement for proper generated sieves.**  The
maximal-sieve case is automatic (previous theorem), so the remaining content is
concentrated on proper covering sieves. -/
theorem S2440SliceEffectiveDescent_iff_proper :
    S2440SliceEffectiveDescent J A ↔
      ∀ (S : C) (R : Presieve S), Sieve.generate R ∈ J S → Sieve.generate R ≠ ⊤ →
        HasEffectiveDescentPresieve (J.pseudofunctorOver A) R := by
  constructor
  · intro h S R hR _
    exact h S R hR
  · intro h S R hR
    by_cases htop : Sieve.generate R = ⊤
    · exact S2440SliceEffectiveDescent_of_generate_top J A S R htop
    · exact h S R hR htop

/-- The amalgamation form of the proper-sieve reduction. -/
theorem S2440SliceAmalgamation_iff_proper :
    S2440SliceAmalgamation J A ↔
      ∀ (S : C) (R : Presieve S), Sieve.generate R ∈ J S → Sieve.generate R ≠ ⊤ →
        ∀ D : (J.pseudofunctorOver A).DescentData (fun (g : R.category) => g.obj.hom),
          Nonempty (Amalgam (J.pseudofunctorOver A) (fun (g : R.category) => g.obj.hom) D) := by
  rw [← S2440SliceEffectiveDescent_iff_amalgamation, S2440SliceEffectiveDescent_iff_proper]
  constructor
  · intro h S R hR hne D
    exact (hasEffectiveDescent_iff_amalgam (J.pseudofunctorOver A)
      (fun (g : R.category) => g.obj.hom)).mp (h S R hR hne) D
  · intro h S R hR hne
    exact (hasEffectiveDescent_iff_amalgam (J.pseudofunctorOver A)
      (fun (g : R.category) => g.obj.hom)).mpr (fun D => h S R hR hne D)

end General

/-! ## 2. The exact missing theorem, over all sites -/

/-- **The exact missing theorem (stack of sheaves on slices, Type-valued).**  For every
site `(C, J)` and every universe `w`, the pseudofunctor
`X |-> Sheaf (J.over X) (Type w)` is a stack for `J`.

This is the precise Mathlib gap behind S2134: Mathlib v4.32.2 has no `IsStack`
instance for any category-valued pseudofunctor.  The statement is the standard descent
theorem for the slice topos (SGA 4; Giraud, *Cohomologie non abelienne*, II 1.2;
Laumon--Moret-Bailly, *Champs algebriques*, 3.2).  It is stated for `Type`-valued
sheaves because that is the target of `S2029SheafPrestack`; for a general target
category `A` the analogous statement needs the relevant limits in `A`, and it
already fails for the empty target category on a topology in which the empty sieve is
covering; hence no general-`A` all-sites version is asserted here. -/
def S2440SliceSheafStackAll : Prop :=
  ∀ (C : Type u) [Category.{v} C] (J : GrothendieckTopology C),
    S2440SliceStack (C := C) J (Type w)

/-- The prestack half over all sites (the S2103-type naturality input), Type-valued. -/
def S2440SliceSheafPrestackAll : Prop :=
  ∀ (C : Type u) [Category.{v} C] (J : GrothendieckTopology C),
    S2440SlicePrestack (C := C) J (Type w)

/-- **The effective-descent half of the exact missing theorem, over all sites.**  This
single statement is the exact missing mathematical input. -/
def S2440SliceSheafEffectiveDescentAll : Prop :=
  ∀ (C : Type u) [Category.{v} C] (J : GrothendieckTopology C),
    S2440SliceEffectiveDescent (C := C) J (Type w)

/-- The amalgamation form of the exact missing theorem, over all sites. -/
def S2440SliceSheafAmalgamationAll : Prop :=
  ∀ (C : Type u) [Category.{v} C] (J : GrothendieckTopology C),
    S2440SliceAmalgamation (C := C) J (Type w)

/-- The effective-descent half and the amalgamation form of the missing theorem are
equivalent, over all sites. -/
theorem S2440SliceSheafEffectiveDescentAll_iff_amalgamation :
    S2440SliceSheafEffectiveDescentAll.{v, u, w} ↔
      S2440SliceSheafAmalgamationAll.{v, u, w} := by
  constructor
  · intro h C _ J
    exact (S2440SliceEffectiveDescent_iff_amalgamation J (Type w)).mp (h C J)
  · intro h C _ J
    exact (S2440SliceEffectiveDescent_iff_amalgamation J (Type w)).mpr (h C J)

/-- **Exact decomposition of the missing theorem, over all sites.** -/
theorem S2440SliceSheafStackAll_iff :
    S2440SliceSheafStackAll.{v, u, w} ↔
      S2440SliceSheafPrestackAll.{v, u, w} ∧
        S2440SliceSheafEffectiveDescentAll.{v, u, w} := by
  constructor
  · intro h
    exact ⟨fun C _ J => ((S2440SliceStack_iff (C := C) J (Type w)).mp (h C J)).1,
      fun C _ J => ((S2440SliceStack_iff (C := C) J (Type w)).mp (h C J)).2⟩
  · rintro ⟨hP, hE⟩ C _ J
    exact (S2440SliceStack_iff (C := C) J (Type w)).mpr ⟨hP C J, hE C J⟩

/-- The amalgamation form of the exact decomposition. -/
theorem S2440SliceSheafStackAll_iff_amalgamation :
    S2440SliceSheafStackAll.{v, u, w} ↔
      S2440SliceSheafPrestackAll.{v, u, w} ∧
        S2440SliceSheafAmalgamationAll.{v, u, w} := by
  rw [S2440SliceSheafStackAll_iff, S2440SliceSheafEffectiveDescentAll_iff_amalgamation]

/-- The exact missing theorem, named for the D9 consumer.  This is the single
mathematical input that S2134 leaves open. -/
def S2440FirstMissing : Prop := S2440SliceSheafStackAll.{v, u, w}

/-- The effective-descent half of the exact missing theorem, named. -/
def S2440FirstMissingEffectiveDescent : Prop :=
  S2440SliceSheafEffectiveDescentAll.{v, u, w}

/-! ## 3. The D9 site: deduction of the target from the exact missing theorem -/

section Field

variable {K : Type u} [Field K]

/-- The D9 site instance of the stack-of-slice-sheaves theorem: the slice-sheaf
prestack is an etale stack. -/
def S2440EtaleSliceStack (K : Type u) [Field K] : Prop :=
  (S2029SheafPrestack K).IsStack (Iut.SchemeOverField.etaleTopology K)

/-- **The etale-site effective-descent statement on all covering sieves.**  This is
the half of the D9 stack theorem which is exactly the target: it implies
`S2134EffDescentOnEtaleFamilies K` without any further input, and conversely
the target plus the prestack half implies it. -/
def S2440EtaleSliceEffectiveDescent (K : Type u) [Field K] : Prop :=
  ∀ (S : Iut.SchemeOverField K) (R : Sieve S),
    R ∈ Iut.SchemeOverField.etaleTopology K S →
      ((S2029SheafPrestack K).toDescentData
        (fun (g : R.arrows.category) => g.obj.hom)).EssSurj

/-- The etale-site effective-descent statement is the S2093 effective-descent half,
by definition. -/
theorem S2440EtaleSliceEffectiveDescent_iff_S2093 :
    S2440EtaleSliceEffectiveDescent (K := K) ↔ S2093SheafEffectiveDescent (K := K) :=
  Iff.rfl

/-- The D9 named first missing in effective-descent form: the etale-site effective
descent on all covering sieves.  It implies the target and is implied by
target + prestack. -/
def S2440EtaleFirstMissing (K : Type u) [Field K] : Prop :=
  S2440EtaleSliceEffectiveDescent (K := K)

/-- **The etale-site effective descent on all covering sieves implies the target.**
No prestack hypothesis is used. -/
theorem S2440EtaleSliceEffectiveDescent_to_target
    (h : S2440EtaleSliceEffectiveDescent (K := K)) :
    S2134EffDescentOnEtaleFamilies (K := K) := by
  intro S R hR
  have hgen : Sieve.generate R ∈ Iut.SchemeOverField.etaleTopology K S := by
    rw [← S2093EtalePrecoverage_toGrothendieck (K := K)]
    exact Precoverage.generate_mem_toGrothendieck hR
  have h' : HasEffectiveDescentPresieve (S2029SheafPrestack K)
      (Sieve.generate R).arrows :=
    h S (Sieve.generate R) hgen
  exact (hasEffectiveDescentPresieve_iff_of_generate_eq (F := S2029SheafPrestack K)
    (R := R) (R' := (Sieve.generate R).arrows) (by rw [Sieve.generate_sieve])).mpr h'

/-- Conversely, the target plus the prestack half gives the etale-site effective
descent on all covering sieves (S2134/S2093 reduction). -/
theorem S2440EtaleSliceEffectiveDescent_of_target_and_prestack
    (hP : S2093SheafPrestack (K := K))
    (hE : S2134EffDescentOnEtaleFamilies (K := K)) :
    S2440EtaleSliceEffectiveDescent (K := K) :=
  S2093SheafEffectiveDescent_of_prestack_and_families hP hE

/-- **The D9 stack theorem is exactly the prestack half plus the target.** -/
theorem S2440EtaleSliceStack_iff :
    S2440EtaleSliceStack (K := K) ↔
      S2093SheafPrestack (K := K) ∧ S2134EffDescentOnEtaleFamilies (K := K) := by
  constructor
  · intro h
    exact ⟨h.toIsPrestack,
      S2134EffDescentOnEtaleFamilies_of_effectiveDescent
        (fun S R hR => h.essSurj_of_sieve R hR)⟩
  · rintro ⟨hP, hE⟩
    have hD := S2093SheafEffectiveDescent_of_prestack_and_families hP hE
    haveI : (S2029SheafPrestack K).IsPrestack
        (Iut.SchemeOverField.etaleTopology K) := hP
    refine Pseudofunctor.IsStack.of_isStackFor (F := S2029SheafPrestack K) ?_
    intro S R hR
    rw [Pseudofunctor.isStackFor_iff]
    have hff := Pseudofunctor.fullyFaithfulToDescentData
      (F := S2029SheafPrestack K) (f := fun (g : R.arrows.category) => g.obj.hom)
      (J := Iut.SchemeOverField.etaleTopology K)
      (by rw [Sieve.ofArrows_category', Sieve.generate_sieve]; exact hR)
    exact { faithful := hff.faithful, full := hff.full, essSurj := hD S R hR }

/-- The stack theorem is exactly the prestack half plus effective descent on all
covering sieves. -/
theorem S2440EtaleSliceStack_iff_effectiveDescent :
    S2440EtaleSliceStack (K := K) ↔
      S2093SheafPrestack (K := K) ∧ S2440EtaleSliceEffectiveDescent (K := K) := by
  constructor
  · intro h
    exact ⟨h.toIsPrestack, fun S R hR => h.essSurj_of_sieve R hR⟩
  · rintro ⟨hP, hD⟩
    exact (S2440EtaleSliceStack_iff).mpr
      ⟨hP, S2440EtaleSliceEffectiveDescent_to_target hD⟩

/-- **Non-vacuity at the actual etale site**: every presieve whose generated sieve is
maximal has effective descent for the slice-sheaf prestack, unconditionally. -/
theorem S2440EtaleSliceEffectiveDescent_of_generate_top
    (S : Iut.SchemeOverField K) (R : Presieve S) (hR : Sieve.generate R = ⊤) :
    HasEffectiveDescentPresieve (S2029SheafPrestack K) R :=
  hasEffectiveDescentPresieve_of_generate_top (S2029SheafPrestack K) R hR

/-- The target in the amalgamation interface form recorded by S2439 (re-export of the
actual equivalence). -/
theorem S2440Target_iff_interface :
    S2134EffDescentOnEtaleFamilies (K := K) ↔ S2439AmalgamationInterface (K := K) :=
  S2439EffDescent_iff_amalgamation (K := K)

/-! ### 3a. The exact missing theorem implies the D9 target -/

/-- The all-sites stack theorem, at the universes of the D9 site, gives the D9 stack
theorem. -/
theorem S2440EtaleSliceStack_of_allSites
    (h : S2440SliceSheafStackAll.{u, u+1, u}) :
    S2440EtaleSliceStack (K := K) :=
  h (Iut.SchemeOverField K) (Iut.SchemeOverField.etaleTopology K) (Type u)

/-- The effective-descent half of the exact missing theorem gives the D9 effective
descent on all covering sieves. -/
theorem S2440EtaleSliceEffectiveDescent_of_allSites
    (h : S2440SliceSheafEffectiveDescentAll.{u, u+1, u}) :
    S2440EtaleSliceEffectiveDescent (K := K) := by
  intro S R hR
  exact h (Iut.SchemeOverField K) (Iut.SchemeOverField.etaleTopology K) (Type u)
    S R.arrows (by rwa [Sieve.generate_sieve])

/-- **The exact missing theorem implies the D9 target.** -/
theorem S2440ExactMissing_to_target
    (h : S2440SliceSheafStackAll.{u, u+1, u}) :
    S2134EffDescentOnEtaleFamilies (K := K) :=
  S2440EtaleSliceEffectiveDescent_to_target
    (S2440EtaleSliceEffectiveDescent_of_allSites
      (fun C _ J A _ => ((S2440SliceStack_iff (C := C) J A).mp (h C J A)).2))

/-- **The amalgamation form of the exact missing theorem implies the D9 interface.**
This is the literal construction requested by `S2439AmalgamationInterface`. -/
theorem S2440ExactMissing_to_interface
    (h : S2440SliceSheafAmalgamationAll.{u, u+1, u}) :
    S2439AmalgamationInterface (K := K) := by
  intro S R hR D
  have hgen : Sieve.generate R ∈ Iut.SchemeOverField.etaleTopology K S := by
    rw [← S2093EtalePrecoverage_toGrothendieck (K := K)]
    exact Precoverage.generate_mem_toGrothendieck hR
  exact h (Iut.SchemeOverField K) (Iut.SchemeOverField.etaleTopology K) (Type u)
    S R hgen D

end Field

/-! ## 4. The exact first missing, and axiom footprint -/

/-- **Exact first missing, in the sharpest usable form.**  It is the effective descent
of the slice-sheaf pseudofunctor over an arbitrary site; at the D9 site it is
`S2440EtaleFirstMissing K` (`S2440EtaleSliceEffectiveDescent K`), which implies the
target `S2134EffDescentOnEtaleFamilies K` unconditionally.

No inhabitant is asserted.  The standard mathematical proof is Cech descent for the
slice topos: for a covering sieve `R` at `S` and a descent datum `(F_i, phi_ij)`, the
amalgam is the sheaf `T |-> lim` of matching families over the pullback of `R` to
`T`; its sheaf property is the transitivity of the topology, and its restriction to
`X_i` is `F_i` by the sheaf condition of `F_i`.  This construction is not formalized
in Mathlib v4.32.2 (there is no `IsStack` instance for a category-valued
pseudofunctor at all). -/
def S2440ExactFirstMissing : Prop :=
  S2440SliceSheafEffectiveDescentAll.{v, u, w}

#check @S2440SliceStack
#check @S2440SlicePrestack
#check @S2440SliceEffectiveDescent
#check @S2440SliceAmalgamation
#check @S2440SliceEffectiveDescent_iff_amalgamation
#check @S2440SliceStack_iff
#check @S2440SliceStack_iff_amalgamation
#check @S2440SliceEffectiveDescent_of_generate_top
#check @S2440SliceAmalgamation_of_generate_top
#check @S2440SliceAmalgamation_bot
#check @S2440SliceEffectiveDescent_iff_proper
#check @S2440SliceAmalgamation_iff_proper
#check @S2440SliceSheafStackAll
#check @S2440SliceSheafPrestackAll
#check @S2440SliceSheafEffectiveDescentAll
#check @S2440SliceSheafAmalgamationAll
#check @S2440SliceSheafEffectiveDescentAll_iff_amalgamation
#check @S2440SliceSheafStackAll_iff
#check @S2440SliceSheafStackAll_iff_amalgamation
#check @S2440FirstMissing
#check @S2440FirstMissingEffectiveDescent
#check @S2440EtaleSliceStack
#check @S2440EtaleSliceEffectiveDescent
#check @S2440EtaleFirstMissing
#check @S2440EtaleSliceEffectiveDescent_iff_S2093
#check @S2440EtaleSliceEffectiveDescent_to_target
#check @S2440EtaleSliceEffectiveDescent_of_target_and_prestack
#check @S2440EtaleSliceStack_iff
#check @S2440EtaleSliceStack_iff_effectiveDescent
#check @S2440EtaleSliceEffectiveDescent_of_generate_top
#check @S2440Target_iff_interface
#check @S2440EtaleSliceStack_of_allSites
#check @S2440EtaleSliceEffectiveDescent_of_allSites
#check @S2440ExactMissing_to_target
#check @S2440ExactMissing_to_interface
#check @S2440ExactFirstMissing

#print axioms S2440SliceEffectiveDescent_iff_amalgamation
#print axioms S2440SliceStack_iff
#print axioms S2440SliceStack_iff_amalgamation
#print axioms S2440SliceEffectiveDescent_of_generate_top
#print axioms S2440SliceAmalgamation_of_generate_top
#print axioms S2440SliceAmalgamation_bot
#print axioms S2440SliceEffectiveDescent_iff_proper
#print axioms S2440SliceAmalgamation_iff_proper
#print axioms S2440SliceSheafEffectiveDescentAll_iff_amalgamation
#print axioms S2440SliceSheafStackAll_iff
#print axioms S2440SliceSheafStackAll_iff_amalgamation
#print axioms S2440EtaleSliceEffectiveDescent_iff_S2093
#print axioms S2440EtaleSliceEffectiveDescent_to_target
#print axioms S2440EtaleSliceEffectiveDescent_of_target_and_prestack
#print axioms S2440EtaleSliceStack_iff
#print axioms S2440EtaleSliceStack_iff_effectiveDescent
#print axioms S2440EtaleSliceEffectiveDescent_of_generate_top
#print axioms S2440Target_iff_interface
#print axioms S2440EtaleSliceStack_of_allSites
#print axioms S2440EtaleSliceEffectiveDescent_of_allSites
#print axioms S2440ExactMissing_to_target
#print axioms S2440ExactMissing_to_interface

end LeanFormal.IUT.XiFPaper.S2440AmalgamationActual

end





