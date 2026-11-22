
import tmp.sheaf.xif.paper.S2103D9PrestackActual

/-!
# S2134: effective descent for the D9 slice-sheaf prestack

The D9 stack target of S2050/S2093 is the assertion that the natural slice-sheaf
prestack

  S2029SheafPrestack K = (etaleTopology K).pseudofunctorOver (Type u)

on the etale site of SchemeOverField K is a stack.  S2093 decomposes it *exactly* into
the two fields of Mathlib's Pseudofunctor.IsStack:

  IsStack  <->  S2093SheafPrestack  /\  S2093SheafEffectiveDescent.

The first half (descent of morphisms) is attacked by S2100/S2103; it reduces to a
naturality input S2103FirstMissing.  The second half - effective descent, i.e.
essential surjectivity of the descent functor on every covering sieve - was *not*
touched by those packages.  This file treats it.

## What is proved here (unconditional, no sorry, no new axiom)

1. *Family form of effective descent.*  For a presieve R at S, effective descent
   means essential surjectivity of toDescentData for the family of all arrows of R
   (HasEffectiveDescentPresieve).  It is *invariant under a change of the presenting
   family*: two families generating the same sieve have equivalent effective descent
   conditions (section 1).  This is the formal content of "effective descent only
   depends on the sieve".
2. *Effective descent = existence of amalgamations.*  For every descent datum, an
   object of the fibre at the base together with an isomorphism of its descent data to
   the given datum.  This is the precise construction which is missing in Mathlib
   (section 1, Amalgam).
3. *Base case: covers refined by the identity have effective descent.*  For an
   arbitrary Cat-valued pseudofunctor and the cover by the identity morphism, every
   descent datum is canonically isomorphic to the descent data of its own object at the
   index of the identity (the comparison being the pseudofunctor unit).  By the
   invariance of (1) this gives effective descent for *every* presieve whose generated
   sieve is maximal, in particular every cover containing a split epimorphism (section
   2).  On the D9 site the identity cover is an actual etale precoverage cover, so the
   effective-descent half is here *proved* for a genuine class of etale covers.
4. *The exact effective-descent half of the D9 stack target, named S2134FirstMissing.*
   S2093SheafEffectiveDescent is equivalent to the presieve form (section 3).  The
   effective-descent condition for all covering sieves implies the condition for the
   actual etale covering families (S2134EffDescentOnEtaleFamilies), and conversely the
   prestack half together with the family form implies the full effective-descent half
   (section 3).  Hence

     S2093LargeSheafStackMissing K
       <-> S2093SheafPrestack K /\ S2134EffDescentOnEtaleFamilies K,

   i.e. the D9 stack target is exactly the prestack half plus effective descent on the
   actual etale covering families.  In particular the S2103 naturality input plus
   S2134EffDescentOnEtaleFamilies proves the D9 stack target (section 3b).

The D9 stack field therefore has exactly two named missing inputs: the prestack half
(S2100/S2103, the naturality of the slice comparison) and the effective-descent half
S2134FirstMissing.  No IsStack instance is produced and no effective-descent statement
is assumed anywhere in this file.

## Honest boundary: what is missing, and why

* The effective-descent half is *not proved for all etale covering families*: what is
  proved is the class of covers refined by the identity (generated sieve maximal,
  section 2).  For a general etale cover (e.g. a nontrivial two-element cover by
  distinct etale maps) the construction of an amalgamation from a descent datum is
  absent.  This is exactly the statement S2134EffDescentOnEtaleFamilies K recorded in
  section 3, equivalently the amalgamation statement of section 1.
* Mathlib v4.32.2 contains no instance of Pseudofunctor.IsStack at all: the only
  occurrences of the class in the library are its definition, the projection lemmas,
  and the constructors IsStack.of_isStackFor / IsStack.of_precoverage, which both take
  the stack condition itself as a hypothesis.  In particular the "sheaves on slices
  form a stack" theorem is absent.  The missing construction is the one which,
  given a covering family and a descent datum of sheaves on the slice sites, produces
  a sheaf on the slice site of the base with the correct pullbacks; it needs (at
  least) the Cech descent comparison for the slice topos, which is not in Mathlib.
* The base case proved in section 2 is genuinely a *base case*: it uses the index of a
  split epimorphism (or of the identity) to read off the glued object, and therefore
  does not apply to a general etale covering family.  It shows that the
  effective-descent half is not vacuous, and it pins the obstruction to non-split
  covers.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2134D9DescentActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2093D9StackActual
open LeanFormal.IUT.XiFPaper.S2029GiraudStackificationActual
open LeanFormal.IUT.XiFPaper.S2103D9PrestackActual

universe v u v' u'

/-! ## 1. Effective descent for a family and for a presieve -/

section General

variable {C : Type u} [Category.{v} C]
variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})

/-- Effective descent for a family of morphisms: every descent datum relative to the
family is isomorphic to the descent datum of an actual object of the fibre at the base. -/
def HasEffectiveDescent {ι : Type*} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) : Prop :=
  (F.toDescentData f).EssSurj

/-- Effective descent for a presieve, i.e. for the family of all its arrows. -/
def HasEffectiveDescentPresieve {S : C} (R : Presieve S) : Prop :=
  (F.toDescentData (fun (g : R.category) => g.obj.hom)).EssSurj

/-- **Invariance of effective descent under a change of the covering family.**
If two families generate the same sieve, then effective descent for one is
equivalent to effective descent for the other.  This is the sharp form of
"effective descent depends only on the sieve, not on the presentation". -/
theorem hasEffectiveDescent_iff_of_sieve_eq {ι : Type*} {S : C} {X : ι → C}
    {f : ∀ i, X i ⟶ S} {ι' : Type*} {X' : ι' → C} {f' : ∀ j, X' j ⟶ S}
    (h : Sieve.ofArrows X f = Sieve.ofArrows X' f') :
    HasEffectiveDescent F f ↔ HasEffectiveDescent F f' := by
  constructor
  · intro hD
    obtain ⟨e, ⟨iso⟩⟩ := Pseudofunctor.DescentData.exists_equivalence_of_sieve_eq F f f' h
    letI : (F.toDescentData f).EssSurj := hD
    have h1 : (F.toDescentData f ⋙ e.functor).EssSurj := Functor.essSurj_comp _ _
    letI := h1
    exact Functor.essSurj_of_iso iso
  · intro hD
    obtain ⟨e, ⟨iso⟩⟩ := Pseudofunctor.DescentData.exists_equivalence_of_sieve_eq F f' f h.symm
    letI : (F.toDescentData f').EssSurj := hD
    have h1 : (F.toDescentData f' ⋙ e.functor).EssSurj := Functor.essSurj_comp _ _
    letI := h1
    exact Functor.essSurj_of_iso iso

/-- Effective descent for a presieve depends only on the sieve it generates. -/
theorem hasEffectiveDescentPresieve_iff_of_generate_eq {S : C} {R R' : Presieve S}
    (h : Sieve.generate R = Sieve.generate R') :
    HasEffectiveDescentPresieve F R ↔ HasEffectiveDescentPresieve F R' := by
  have h' : Sieve.ofArrows _ (fun (g : R.category) => g.obj.hom) =
      Sieve.ofArrows _ (fun (g : R'.category) => g.obj.hom) := by
    rw [Sieve.ofArrows_category', Sieve.ofArrows_category', h]
  exact hasEffectiveDescent_iff_of_sieve_eq F h'

/-- The amalgamation of a descent datum: an actual object of the fibre at the base whose
image under the descent functor is isomorphic to the given datum.  Effective descent is
exactly the statement that every descent datum has an amalgamation. -/
structure Amalgam {ι : Type*} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    (D : F.DescentData f) where
  /-- the object of the fibre at the base that is glued from the descent datum -/
  M : F.obj (.mk (op S))
  /-- the comparison isomorphism with the given descent datum -/
  iso : (F.toDescentData f).obj M ≅ D

/-- **Effective descent = existence of amalgamations.**  This is the precise content
of the missing construction: for every descent datum, produce an object and an
isomorphism to its descent data. -/
theorem hasEffectiveDescent_iff_amalgam {ι : Type*} {S : C} {X : ι → C}
    (f : ∀ i, X i ⟶ S) :
    HasEffectiveDescent F f ↔ ∀ D : F.DescentData f, Nonempty (Amalgam F f D) := by
  constructor
  · intro h D
    letI : (F.toDescentData f).EssSurj := h
    exact ⟨{ M := Functor.objPreimage (F.toDescentData f) D, iso := Functor.objObjPreimageIso (F.toDescentData f) D }⟩
  · intro h
    refine ⟨fun D => ?_⟩
    obtain ⟨A⟩ := h D
    exact ⟨A.M, ⟨A.iso⟩⟩

end General

/-! ## 2. Base case: covers refined by the identity -/

section BaseCase

variable {C : Type u} [Category.{v} C]
variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
variable {S : C}

/-- **The comparison isomorphism for the cover by the identity morphism.**  For an
arbitrary descent datum relative to the singleton family consisting of the identity,
the object at the unique index already determines the descent datum: the comparison is
the pseudofunctor unit F.mapId at S.  This is the formal statement that descent along
the identity is effective. -/
def idFamilyDescentIso (D : F.DescentData (fun (_ : Unit) => (𝟙 S : S ⟶ S))) :
    ((F.toDescentData (fun (_ : Unit) => (𝟙 S : S ⟶ S))).obj (D.obj ())) ≅ D := by
  refine Pseudofunctor.DescentData.isoMk (fun i => ?_) ?_
  · obtain rfl : i = () := Subsingleton.elim i ()
    exact (Cat.Hom.toNatIso (F.mapId (.mk (op S)))).app (D.obj ())
  · intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    obtain rfl : i₁ = i₂ := Subsingleton.elim i₁ i₂
    have h₁ : f₁ = q := by simpa using hf₁
    have h₂ : f₂ = q := by simpa using hf₂
    subst h₁
    subst h₂
    simp [Pseudofunctor.DescentData.hom_self]

/-- **Effective descent for the cover by the identity morphism**, for an arbitrary
category-valued pseudofunctor. -/
theorem hasEffectiveDescent_idFamily :
    HasEffectiveDescent F (fun (_ : Unit) => (𝟙 S : S ⟶ S)) :=
  ⟨fun D => ⟨D.obj (), ⟨idFamilyDescentIso F D⟩⟩⟩

/-- The identity family generates the maximal sieve. -/
theorem sieve_ofArrows_idFamily :
    Sieve.ofArrows (fun (_ : Unit) => S) (fun _ => (𝟙 S : S ⟶ S)) = ⊤ :=
  Sieve.generate_of_contains_isSplitEpi (𝟙 S) (Presieve.ofArrows.mk ())

/-- **Effective descent for every presieve whose generated sieve is maximal.**
This covers all covers refined by the identity, in particular all covers containing a
split epimorphism (e.g. an isomorphism), and shows that the only obstruction to
effective descent for these arguments is the non-split nature of a cover. -/
theorem hasEffectiveDescentPresieve_of_generate_top (R : Presieve S)
    (hR : Sieve.generate R = ⊤) : HasEffectiveDescentPresieve F R := by
  have h := hasEffectiveDescent_iff_of_sieve_eq (F := F)
    (f := fun (_ : Unit) => (𝟙 S : S ⟶ S))
    (f' := fun (g : R.category) => g.obj.hom) ?_
  · exact h.mp (hasEffectiveDescent_idFamily F)
  · rw [sieve_ofArrows_idFamily, Sieve.ofArrows_category', hR]

/-- Effective descent for every cover containing a split epimorphism. -/
theorem hasEffectiveDescentPresieve_of_contains_isSplitEpi {Y : C} (R : Presieve S)
    (f : Y ⟶ S) [IsSplitEpi f] (hf : R f) : HasEffectiveDescentPresieve F R :=
  hasEffectiveDescentPresieve_of_generate_top F R (Sieve.generate_of_contains_isSplitEpi f hf)

/-- **Effective descent for the maximal presieve.**  The top sieve is covering for every
Grothendieck topology; hence the effective-descent half of the D9 target is automatic on
it, and any failure can only occur at a proper covering sieve. -/
theorem hasEffectiveDescentPresieve_top : HasEffectiveDescentPresieve F (⊤ : Presieve S) :=
  hasEffectiveDescentPresieve_of_generate_top F ⊤ Sieve.generate_top

end BaseCase

/-! ## 3. The D9 effective-descent half on the actual etale covering families -/

section Field

variable {K : Type u} [Field K]

/-- **The effective-descent half of D9, in family form.**  For every presieve that is
part of the etale precoverage on the category of schemes over K (i.e. every actual
etale covering family), the descent functor of the slice-sheaf prestack is
essentially surjective. -/
noncomputable def S2134EffDescentOnEtaleFamilies (K : Type u) [Field K] : Prop :=
  ∀ (S : Iut.SchemeOverField K) (R : Presieve S),
    R ∈ (S2093EtalePrecoverage K).coverings S →
      HasEffectiveDescentPresieve (S2029SheafPrestack K) R

/-- **The exact first missing, written with amalgamations.**  Every descent datum on an
actual etale covering family has an amalgamation in the slice-sheaf category over the
base.  This is the construction which Mathlib does not provide. -/
theorem S2134EffDescentOnEtaleFamilies_iff_amalgam :
    S2134EffDescentOnEtaleFamilies (K := K) ↔
      ∀ (S : Iut.SchemeOverField K) (R : Presieve S),
        R ∈ (S2093EtalePrecoverage K).coverings S →
          ∀ D : (S2029SheafPrestack K).DescentData (fun (g : R.category) => g.obj.hom),
            Nonempty (Amalgam (S2029SheafPrestack K) (fun (g : R.category) => g.obj.hom) D) := by
  refine forall_congr' (fun S => forall_congr' (fun R => imp_congr_right (fun hR => ?_)))
  exact hasEffectiveDescent_iff_amalgam (S2029SheafPrestack K) (fun (g : R.category) => g.obj.hom)

/-- **The exact first missing of D9 on the effective-descent side.**  Effective descent
for the actual etale covering families, equivalently (section 1) the existence of
amalgamations for all descent data on those covers.  No inhabitant is asserted. -/
def S2134FirstMissing (K : Type u) [Field K] : Prop :=
  S2134EffDescentOnEtaleFamilies K

/-- The named first missing is the family form. -/
theorem S2134FirstMissing_iff :
    S2134FirstMissing (K := K) ↔ S2134EffDescentOnEtaleFamilies (K := K) := Iff.rfl

/-- The family form restricted to proper generated sieves: the maximal-sieve case is
automatic, so the first missing consists of the proper etale covers. -/
theorem S2134EffDescentOnEtaleFamilies_iff_proper :
    S2134EffDescentOnEtaleFamilies (K := K) ↔
      ∀ (S : Iut.SchemeOverField K) (R : Presieve S),
        R ∈ (S2093EtalePrecoverage K).coverings S →
          Sieve.generate R ≠ ⊤ → HasEffectiveDescentPresieve (S2029SheafPrestack K) R := by
  unfold S2134EffDescentOnEtaleFamilies
  constructor
  · intro h S R hR _
    exact h S R hR
  · intro h S R hR
    by_cases htop : Sieve.generate R = ⊤
    · exact hasEffectiveDescentPresieve_of_generate_top _ R htop
    · exact h S R hR htop

/-- The identity cover is an actual etale precoverage cover (the precoverage has
isomorphisms) and it has effective descent. -/
theorem S2134EffDescent_identityCover (S : Iut.SchemeOverField K) :
    Presieve.singleton (𝟙 S) ∈ (S2093EtalePrecoverage K).coverings S ∧
      HasEffectiveDescentPresieve (S2029SheafPrestack K) (Presieve.singleton (𝟙 S)) :=
  ⟨Precoverage.mem_coverings_of_isIso (𝟙 S),
    hasEffectiveDescentPresieve_of_generate_top (S2029SheafPrestack K) _
      (Sieve.generate_of_singleton_isSplitEpi (𝟙 S))⟩

/-- The same for every cover that contains a split epimorphism: effective descent holds,
unconditionally. -/
theorem S2134EffDescent_of_contains_isSplitEpi {S : Iut.SchemeOverField K}
    (R : Presieve S) {Y : Iut.SchemeOverField K} (f : Y ⟶ S) [IsSplitEpi f] (hf : R f) :
    HasEffectiveDescentPresieve (S2029SheafPrestack K) R :=
  hasEffectiveDescentPresieve_of_contains_isSplitEpi (S2029SheafPrestack K) R f hf

/-! ### 3a. The target in presieve form -/

/-- **The effective-descent half of the D9 stack target, in presieve form.**  The
condition on covering sieves is equivalent to the same condition on presieves whose
generated sieve is covering. -/
theorem S2093SheafEffectiveDescent_iff_presieve_form :
    S2093SheafEffectiveDescent (K := K) ↔
      ∀ (S : Iut.SchemeOverField K) (R : Presieve S),
        Sieve.generate R ∈ Iut.SchemeOverField.etaleTopology K S →
          HasEffectiveDescentPresieve (S2029SheafPrestack K) R := by
  constructor
  · intro h S R hR
    have h1 : HasEffectiveDescentPresieve (S2029SheafPrestack K) (Sieve.generate R).arrows :=
      h S (Sieve.generate R) hR
    refine (hasEffectiveDescentPresieve_iff_of_generate_eq (F := S2029SheafPrestack K) ?_).mpr h1
    rw [Sieve.generate_sieve]
  · intro h S R hR
    exact h S R.arrows (by rwa [Sieve.generate_sieve])

/-- **Sharpening: only proper covering presieves matter.**  Presieves whose generated
sieve is maximal have effective descent (section 2), so the effective-descent half of
the D9 target is equivalent to its restriction to proper covering presieves.  This is
the sharp form of the exact first missing. -/
theorem S2093SheafEffectiveDescent_iff_proper_presieves :
    S2093SheafEffectiveDescent (K := K) ↔
      ∀ (S : Iut.SchemeOverField K) (R : Presieve S),
        Sieve.generate R ∈ Iut.SchemeOverField.etaleTopology K S →
          Sieve.generate R ≠ ⊤ → HasEffectiveDescentPresieve (S2029SheafPrestack K) R := by
  rw [S2093SheafEffectiveDescent_iff_presieve_form]
  constructor
  · intro h S R hR _
    exact h S R hR
  · intro h S R hR
    by_cases htop : Sieve.generate R = ⊤
    · exact hasEffectiveDescentPresieve_of_generate_top _ R htop
    · exact h S R hR htop

/-- Effective descent on all covering sieves implies effective descent on the actual
etale covering families. -/
theorem S2134EffDescentOnEtaleFamilies_of_effectiveDescent
    (h : S2093SheafEffectiveDescent (K := K)) : S2134EffDescentOnEtaleFamilies (K := K) := by
  intro S R hR
  have hgen : Sieve.generate R ∈ Iut.SchemeOverField.etaleTopology K S := by
    rw [← S2093EtalePrecoverage_toGrothendieck (K := K)]
    exact Precoverage.generate_mem_toGrothendieck hR
  exact (S2093SheafEffectiveDescent_iff_presieve_form (K := K)).mp h S R hgen

/-- The D9 stack missing implies the effective-descent first missing, hence also the
prestack half and the family form together are equivalent to the full D9 stack
missing (see section 3b). -/
theorem S2134FirstMissing_of_stackMissing (h : S2093LargeSheafStackMissing (K := K)) :
    S2134FirstMissing (K := K) :=
  S2134EffDescentOnEtaleFamilies_of_effectiveDescent
    ((S2093LargeSheafStackMissing_iff_decomposition (K := K)).mp h).2

/-- **The prestack half together with effective descent on the actual etale covering
families gives the effective-descent half of the D9 stack target.** -/
theorem S2093SheafEffectiveDescent_of_prestack_and_families
    (hP : S2093SheafPrestack (K := K)) (hE : S2134EffDescentOnEtaleFamilies (K := K)) :
    S2093SheafEffectiveDescent (K := K) := by
  haveI : (S2029SheafPrestack K).IsPrestack (Iut.SchemeOverField.etaleTopology K) := hP
  have hStack : (S2029SheafPrestack K).IsStack (Iut.SchemeOverField.etaleTopology K) := by
    rw [← S2093EtalePrecoverage_toGrothendieck (K := K)]
    refine Pseudofunctor.IsStack.of_precoverage (F := S2029SheafPrestack K)
      (J := S2093EtalePrecoverage K) ?_
    intro S R hR
    have hJ : Sieve.ofArrows _ (fun (g : R.category) => g.obj.hom) ∈
        Iut.SchemeOverField.etaleTopology K S := by
      rw [Sieve.ofArrows_category', ← S2093EtalePrecoverage_toGrothendieck (K := K)]
      exact Precoverage.generate_mem_toGrothendieck hR
    have hff := (S2029SheafPrestack K).fullyFaithfulToDescentData
      (fun (g : R.category) => g.obj.hom) hJ
    exact ⟨{ faithful := hff.faithful, full := hff.full, essSurj := hE S R hR }⟩
  intro U R hR
  exact hStack.essSurj_of_sieve R hR

/-! ### 3b. Decomposition of the D9 stack target into the two named inputs -/

/-- **The D9 stack target is exactly the prestack half plus effective descent on the
actual etale covering families.**  The prestack half is the S2103 naturality input;
the effective-descent half is S2134EffDescentOnEtaleFamilies. -/
theorem S2093LargeSheafStackMissing_iff_halves :
    S2093LargeSheafStackMissing (K := K) ↔
      S2093SheafPrestack (K := K) ∧ S2134EffDescentOnEtaleFamilies (K := K) := by
  constructor
  · intro h
    obtain ⟨hP, hD⟩ := (S2093LargeSheafStackMissing_iff_decomposition (K := K)).mp h
    exact ⟨hP, S2134EffDescentOnEtaleFamilies_of_effectiveDescent hD⟩
  · rintro ⟨hP, hE⟩
    exact (S2093LargeSheafStackMissing_iff_decomposition (K := K)).mpr
      ⟨hP, S2093SheafEffectiveDescent_of_prestack_and_families hP hE⟩

/-- The same decomposition for the family-level stack condition of S2093. -/
theorem S2093SheafStackOnEtaleFamilies_iff_halves :
    S2093SheafStackOnEtaleFamilies (K := K) ↔
      S2093SheafPrestack (K := K) ∧ S2134EffDescentOnEtaleFamilies (K := K) := by
  rw [← S2093SheafStackOnEtaleFamilies_iff (K := K)]
  exact S2093LargeSheafStackMissing_iff_halves (K := K)

/-- **The D9 stack target from the two named inputs.**  The S2103 naturality input
(the prestack half) and effective descent on the actual etale covering families
together prove the D9 stack missing.  No IsStack instance is produced. -/
theorem S2093LargeSheafStackMissing_of_naturality_and_families
    (hN : S2103FirstMissing K) (hE : S2134EffDescentOnEtaleFamilies (K := K)) :
    S2093LargeSheafStackMissing (K := K) :=
  (S2093LargeSheafStackMissing_iff_halves (K := K)).mpr
    ⟨S2093SheafPrestack_of_firstMissing (K := K) hN, hE⟩

end Field

/-! ## 4. Axiom footprint and interface checks -/

#check @hasEffectiveDescent_iff_of_sieve_eq
#check @hasEffectiveDescentPresieve_iff_of_generate_eq
#check @hasEffectiveDescent_iff_amalgam
#check @idFamilyDescentIso
#check @hasEffectiveDescent_idFamily
#check @sieve_ofArrows_idFamily
#check @hasEffectiveDescentPresieve_of_generate_top
#check @hasEffectiveDescentPresieve_of_contains_isSplitEpi
#check @S2134EffDescentOnEtaleFamilies
#check @S2134EffDescentOnEtaleFamilies_iff_amalgam
#check @S2134FirstMissing
#check @S2134FirstMissing_iff
#check @S2134FirstMissing_of_stackMissing
#check @hasEffectiveDescentPresieve_top
#check @S2093SheafEffectiveDescent_iff_proper_presieves
#check @S2134EffDescentOnEtaleFamilies_iff_proper
#check @S2134EffDescent_identityCover
#check @S2134EffDescent_of_contains_isSplitEpi
#check @S2093SheafEffectiveDescent_iff_presieve_form
#check @S2134EffDescentOnEtaleFamilies_of_effectiveDescent
#check @S2093SheafEffectiveDescent_of_prestack_and_families
#check @S2093LargeSheafStackMissing_iff_halves
#check @S2093SheafStackOnEtaleFamilies_iff_halves
#check @S2093LargeSheafStackMissing_of_naturality_and_families

#print axioms hasEffectiveDescent_iff_of_sieve_eq
#print axioms hasEffectiveDescentPresieve_iff_of_generate_eq
#print axioms hasEffectiveDescent_iff_amalgam
#print axioms idFamilyDescentIso
#print axioms hasEffectiveDescent_idFamily
#print axioms sieve_ofArrows_idFamily
#print axioms hasEffectiveDescentPresieve_of_generate_top
#print axioms hasEffectiveDescentPresieve_of_contains_isSplitEpi
#print axioms S2134EffDescentOnEtaleFamilies_iff_amalgam
#print axioms S2134FirstMissing_of_stackMissing
#print axioms hasEffectiveDescentPresieve_top
#print axioms S2093SheafEffectiveDescent_iff_proper_presieves
#print axioms S2134EffDescentOnEtaleFamilies_iff_proper
#print axioms S2134EffDescent_identityCover
#print axioms S2134EffDescent_of_contains_isSplitEpi
#print axioms S2093SheafEffectiveDescent_iff_presieve_form
#print axioms S2134EffDescentOnEtaleFamilies_of_effectiveDescent
#print axioms S2093SheafEffectiveDescent_of_prestack_and_families
#print axioms S2093LargeSheafStackMissing_iff_halves
#print axioms S2093SheafStackOnEtaleFamilies_iff_halves
#print axioms S2093LargeSheafStackMissing_of_naturality_and_families

end LeanFormal.IUT.XiFPaper.S2134D9DescentActual