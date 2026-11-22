import tmp.sheaf.xif.paper.S2050D9UniverseChoiceActual
import Mathlib.CategoryTheory.Sites.Descent.Precoverage
import Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# S2093: the D9 exact missing -- large sheaf prestack IsStack, or S2029SmallModel + transport

This package attacks the D9 first missing recorded by S2050: the natural slice-sheaf
prestack

  S2050LargeSheafPrestack K = S2029SheafPrestack K :
     Pseudofunctor (LocallyDiscrete (SchemeOverField K)^op) Cat.{u+1,u+1}

(given by GrothendieckTopology.pseudofunctorOver (Type u)) is an etale stack.  The
alternative, if the old Cat.{u,u} target is kept, is a small model of every fibre
together with a transport of the pseudofunctorial structure.

## What is proved here (all unconditional, no sorry, no new axiom)

1. The exact target is restated as S2093LargeSheafStackMissing K, and identified
   definitionally with S2029SheafStack K and with the IsStack assertion for
   S2029SheafPrestack K (section 1).
2. Mathlib's IsStack is decomposed *exactly* into its two fields:
   IsPrestack (descent of morphisms / the hom-presheaves are sheaves) and effective
   descent (essential surjectivity of toDescentData on every covering sieve).
   Both halves are named as S2093SheafPrestack and
   S2093SheafEffectiveDescent; the decomposition is an Iff
   (section 2).
3. The target is reduced from arbitrary covering *sieves* to the actual etale
   *covering families* (the precoverage generating SchemeOverField.etaleTopology).
   This uses Pseudofunctor.IsStack.of_precoverage and an explicit construction of
   the precoverage on Over (Spec K) as the comap of Scheme.etalePrecoverage along
   Over.forget (Spec K).  The reduced target S2093SheafStackOnEtaleFamilies is
   equivalent to the full target (section 3).  This is the sharpest exact form of the
   D9 first missing currently available.
4. S2050LargeCFData l A is decomposed: the stack field is *independent* of the
   quotient data, so the old structure is equivalent to
   Nonempty (S2050LargeEtaleStackOverField F) /\ Nonempty (S1964HonestCFQuotient l A)
   (section 4).  This shows the old target does not tie the stack to the D9 quotient.
5. A corrected exact target S2093LargeCFDataExact l A is introduced: the stack is
   fixed to be the natural sheaf prestack, and the quotient data carry the honest
   signature (0;[2,2,2];1).  We prove
   Nonempty (S2093LargeCFDataExact l A) <->
      S2050LargeSheafStackMissing F /\ Nonempty (S1964HonestCFQuotient l A)
   and that it maps to the old S2050LargeCFData and to S1964QuotientStructure
   (sections 4--5).
6. For the old Cat.{u,u} target we prove
   S2050LargeSheafSmallModel K <-> forall U, Nonempty (S2029SmallModel ... U)
   (this uses Classical.choice), introduce the exact transport input
   S2093SmallStackTransport K (a Cat.{u,u}-valued etale stack with pointwise
   equivalences to the large prestack), and prove that it implies the small-model
   input of S2029/S2050 (section 6).

## Honest boundary: nothing here fabricates the stack

No IsStack instance is produced.  Mathlib v4.32.2 has no IsStack instance at all
for a category-valued pseudofunctor; in particular the "sheaves form a stack"
theorem for U |-> Sheaf (J.over U) A is absent.  The tree's unconditional IsStack
results available here are for representable (discrete) pseudofunctors or degenerate
constant pseudofunctors (terminal, O1ConstructedStack); none of them is the
slice-sheaf prestack.  In particular:

* the prestack half S2093SheafPrestack is *not* proved here; it is one of the two
  named missing inputs, now stated as "all hom-presheaves of slice sheaves are
  sheaves";
* the effective-descent half S2093SheafEffectiveDescent is *not* proved here
  either; after section 3 it is equivalent to effective descent for the actual etale
  covering families S2093SheafStackOnEtaleFamilies;
* for the old target, S2093SmallStackTransport is the exact missing; the pointwise
  small-model proposition S2050LargeSheafSmallModel alone is strictly weaker than
  it because no transport of the pseudofunctorial structure is constructed here.

No pointwise fibration, no label-only quotient, no Shrink/ULift fake is used.
The only axioms are propext, Classical.choice, Quot.sound.

## Research note: the exact next step for the prestack half

Mathlib's CategoryTheory.SheafHom proves that for any site (C,J) and sheaves F G,
the presheaf presheafHom F G is a sheaf, and packages it as sheafHom F G.  For the
slice site (Over S, J.over S), sheafHom M N is a sheaf on Over S whose value at an
object j is Hom(overPullback_j M, overPullback_j N).  The pseudofunctor's own
F.presheafHom instead uses overMapPullback j.hom.  The definitional identity
Over.iteratedSliceBackward_forget identifies Over.forget j with
iteratedSliceBackward j >> Over.map j.hom, and Over.iteratedSliceEquivOverMapIso /
Over.iteratedSliceForwardNaturalityIso give the compatibility of these
identifications with morphisms of Over S; since iteratedSliceEquiv j is an
equivalence, the relevant Hom sets are equivalent.  What is not formalized in the
present file is the naturality in j of this pointwise equivalence, i.e. a natural
isomorphism between Pseudofunctor.presheafHom M N and the underlying presheaf of
SheafHom.sheafHom M N on Over S.  Supplying that natural isomorphism would prove
S2093SheafPrestack; effective descent (S2093SheafEffectiveDescent) is untouched by
this argument.

## Target-change proposal

* Proposal B (recommended): adopt the large exact target S2093LargeCFDataExact l A
  as the D9 receiver.  Its first missing is exactly
  S2050LargeSheafStackMissing (S1732A l).F together with the S1964 honest quotient
  Nonempty (S1964HonestCFQuotient l A).  The stack half is equivalent to effective
  descent for etale covering families (section 3).
* Proposal A (old target): keep Cat.{u,u}; the first missing is
  S2093SmallStackTransport K, i.e. a small etale stack with pointwise equivalences
  to the large slice-sheaf prestack.  S2029SmallModel for all fibres is necessary
  but not sufficient because the transport is not constructed.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.S2093D9StackActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2029GiraudStackificationActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S1983EtThSignatureBridgeActual
open LeanFormal.IUT.XiFPaper.S1964QuotientCFActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1732SourceAssemblyActual
open LeanFormal.IUT.XiFPaper.S1994KSideCovers
open LeanFormal.IUT.XiFPaper.S2050D9UniverseChoiceActual

universe u

variable {K : Type u} [Field K]

/-! ## 1. The exact target and its existing forms -/

/-- S2093's exact D9 stack target: the natural slice-sheaf prestack is an etale
stack.  This is definitionally S2050LargeSheafStackMissing K and
S2029SheafStack K. -/
def S2093LargeSheafStackMissing (K : Type u) [Field K] : Prop :=
  S2050LargeSheafStackMissing K

/-- The exact target is S2050's missing. -/
theorem S2093LargeSheafStackMissing_iff_S2050 :
    S2093LargeSheafStackMissing K ↔ S2050LargeSheafStackMissing K := Iff.rfl

/-- The exact target is S2029's S2029SheafStack. -/
theorem S2093LargeSheafStackMissing_iff_S2029 :
    S2093LargeSheafStackMissing K ↔ S2029SheafStack K := Iff.rfl

/-- The exact target, unfolded to Mathlib's IsStack. -/
theorem S2093LargeSheafStackMissing_iff_IsStack :
    S2093LargeSheafStackMissing K ↔
      (S2029SheafPrestack K).IsStack (Iut.SchemeOverField.etaleTopology K) := Iff.rfl

/-- The underlying object is the actual large-valued slice-sheaf prestack. -/
theorem S2093LargeSheafPrestack_eq :
    S2050LargeSheafPrestack K = S2029SheafPrestack K := rfl

/-- At every test object the prestack takes the actual slice-sheaf category, which
lives in Cat.{u+1,u+1}. -/
theorem S2093LargeSheafPrestack_obj (U : Iut.SchemeOverField K) :
    (S2050LargeSheafPrestack K).obj (LocallyDiscrete.mk (Opposite.op U)) =
      S2029SliceSheafCategory K U :=
  S2029SheafPrestack_obj K U

/-! ## 2. The exact decomposition of IsStack -/

/-- The first half of the stack condition: descent of morphisms.  Concretely, for
every test object S and every pair of slice sheaves M N, the presheaf
F.presheafHom M N on the slice site over S is a sheaf. -/
def S2093SheafPrestack (K : Type u) [Field K] : Prop :=
  (S2029SheafPrestack K).IsPrestack (Iut.SchemeOverField.etaleTopology K)

/-- The second half of the stack condition: effective descent, i.e. the descent
functor toDescentData is essentially surjective on every covering sieve. -/
def S2093SheafEffectiveDescent (K : Type u) [Field K] : Prop :=
  ∀ (U : Iut.SchemeOverField K) (R : Sieve U),
    R ∈ Iut.SchemeOverField.etaleTopology K U →
      ((S2029SheafPrestack K).toDescentData
        (fun f : R.arrows.category => f.obj.hom)).EssSurj

/-- **Exact decomposition of the D9 exact missing.**  Mathlib's IsStack is a
structure with exactly two fields, so the target is the conjunction of the prestack
condition and effective descent.  This is an iff, not a one-way reduction. -/
theorem S2093LargeSheafStackMissing_iff_decomposition :
    S2093LargeSheafStackMissing K ↔
      S2093SheafPrestack K ∧ S2093SheafEffectiveDescent K := by
  change (S2029SheafPrestack K).IsStack (Iut.SchemeOverField.etaleTopology K) ↔ _
  constructor
  · intro h
    refine ⟨h.toIsPrestack, ?_⟩
    intro U R hR
    exact h.essSurj_of_sieve R hR
  · rintro ⟨hP, hD⟩
    refine { toIsPrestack := hP, essSurj_of_sieve := ?_ }
    intro S R hR
    exact hD S R hR

/-- The prestack half written as the concrete sheaf condition on hom-presheaves:
this is the exact content of the first missing half. -/
theorem S2093SheafPrestack_iff_presheafHom :
    S2093SheafPrestack K ↔
      ∀ (S : Iut.SchemeOverField K)
        (M N : (S2029SheafPrestack K).obj (LocallyDiscrete.mk (Opposite.op S))),
        Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology K).over S)
          ((S2029SheafPrestack K).presheafHom M N) := by
  constructor
  · intro h S M N
    exact h.isSheaf M N
  · intro h
    exact ⟨fun {S} M N => h S M N⟩

/-! ## 3. Reduction to the actual etale covering families

SchemeOverField.etaleTopology K is the over-topology of Scheme.etaleTopology at
Spec K, and Scheme.etaleTopology is generated by Scheme.etalePrecoverage.  Pulling
the precoverage back along Over.forget (Spec K) gives a precoverage on
SchemeOverField K that generates the etale topology.  The lemma
Pseudofunctor.IsStack.of_precoverage then reduces the stack condition on arbitrary
sieves to the descent condition on the actual etale covering presieves. -/

set_option backward.isDefEq.respectTransparency false in
/-- Scheme.etalePrecoverage has isomorphisms: it is the inf of the jointly
surjective precoverage and the etale morphism-property precoverage, both of which
have them. -/
instance S2093SchemeEtalePrecoverage_hasIsos :
    AlgebraicGeometry.Scheme.etalePrecoverage.HasIsos := by
  change (AlgebraicGeometry.Scheme.jointlySurjectivePrecoverage ⊓
    (MorphismProperty.precoverage @AlgebraicGeometry.Etale)).HasIsos
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Scheme.etalePrecoverage is stable under composition. -/
instance S2093SchemeEtalePrecoverage_stableComp :
    AlgebraicGeometry.Scheme.etalePrecoverage.IsStableUnderComposition := by
  change (AlgebraicGeometry.Scheme.jointlySurjectivePrecoverage ⊓
    (MorphismProperty.precoverage @AlgebraicGeometry.Etale)).IsStableUnderComposition
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Scheme.etalePrecoverage is stable under base change. -/
instance S2093SchemeEtalePrecoverage_stableBase :
    AlgebraicGeometry.Scheme.etalePrecoverage.IsStableUnderBaseChange := by
  change (AlgebraicGeometry.Scheme.jointlySurjectivePrecoverage ⊓
    (MorphismProperty.precoverage @AlgebraicGeometry.Etale)).IsStableUnderBaseChange
  infer_instance

/-- The etale precoverage on SchemeOverField K, obtained as the comap of the etale
precoverage on schemes along the forgetful functor. -/
noncomputable def S2093EtalePrecoverage (K : Type u) [Field K] :
    Precoverage (Iut.SchemeOverField K) :=
  AlgebraicGeometry.Scheme.etalePrecoverage.comap
    (Over.forget (Spec (CommRingCat.of K)))

set_option backward.isDefEq.respectTransparency false in
instance S2093EtalePrecoverage_hasIsos :
    (S2093EtalePrecoverage K).HasIsos := by
  unfold S2093EtalePrecoverage
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance S2093EtalePrecoverage_stableComp :
    (S2093EtalePrecoverage K).IsStableUnderComposition := by
  unfold S2093EtalePrecoverage
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance S2093EtalePrecoverage_stableBase :
    (S2093EtalePrecoverage K).IsStableUnderBaseChange := by
  unfold S2093EtalePrecoverage
  infer_instance

/-- The pulled-back precoverage generates the actual etale topology on
SchemeOverField K. -/
theorem S2093EtalePrecoverage_toGrothendieck :
    (S2093EtalePrecoverage K).toGrothendieck =
      Iut.SchemeOverField.etaleTopology K := by
  rw [Iut.SchemeOverField.etaleTopology]
  exact (CategoryTheory.over_toGrothendieck_eq_toGrothendieck_comap_forget
    (K := AlgebraicGeometry.Scheme.etalePrecoverage)
    (X := Spec (CommRingCat.of K))).symm

/-- **The exact first missing in family form.**  For every object of the etale site
and every covering presieve from the etale precoverage (an actual etale covering
family), the descent functor for the slice-sheaf prestack is an equivalence. -/
noncomputable def S2093SheafStackOnEtaleFamilies (K : Type u) [Field K] : Prop :=
  ∀ (S : Iut.SchemeOverField K) (R : Presieve S),
    R ∈ (S2093EtalePrecoverage K).coverings S →
      (S2029SheafPrestack K).IsStackFor R

/-- A stack for the etale topology is a stack for every precoverage cover. -/
theorem S2093SheafStackOnEtaleFamilies_of_stack
    (h : S2093LargeSheafStackMissing K) : S2093SheafStackOnEtaleFamilies K := by
  intro S R hR
  have hJ : Sieve.generate R ∈ Iut.SchemeOverField.etaleTopology K S := by
    rw [← S2093EtalePrecoverage_toGrothendieck (K := K)]
    exact Precoverage.generate_mem_toGrothendieck hR
  haveI : (S2029SheafPrestack K).IsStack (Iut.SchemeOverField.etaleTopology K) := h
  exact Pseudofunctor.isStackFor (F := S2029SheafPrestack K) R hJ

/-- A stack for all etale precoverage covers is a stack for the etale topology. -/
theorem S2093LargeSheafStackMissing_of_etaleFamilies
    (h : S2093SheafStackOnEtaleFamilies K) : S2093LargeSheafStackMissing K := by
  change (S2029SheafPrestack K).IsStack (Iut.SchemeOverField.etaleTopology K)
  rw [← S2093EtalePrecoverage_toGrothendieck (K := K)]
  exact Pseudofunctor.IsStack.of_precoverage
    (F := S2029SheafPrestack K) (J := S2093EtalePrecoverage K) h

/-- **The reduced exact target.**  The stack condition on arbitrary covering sieves
is equivalent to effective descent for the actual etale covering families. -/
theorem S2093SheafStackOnEtaleFamilies_iff :
    S2093LargeSheafStackMissing K ↔ S2093SheafStackOnEtaleFamilies K :=
  ⟨S2093SheafStackOnEtaleFamilies_of_stack,
    S2093LargeSheafStackMissing_of_etaleFamilies⟩

/-! ## 4. The old large CFData target: the stack field is independent -/

variable (l : PrimeGeFive) (A : Iut.OrbicurveSignAction S1726Orbicurve)

/-- **Decomposition of the old large CFData.**  The stack field of
S2050LargeCFData is not tied to the quotient data, so the old target is exactly the
product of an arbitrary large etale stack and an S1964 honest quotient.  This is the
precise sense in which the old structure is not yet the D9 exact target. -/
theorem S2093LargeCFData_iff :
    Nonempty (S2050LargeCFData l A) ↔
      Nonempty (S2050LargeEtaleStackOverField (S1732A l).F) ∧
        Nonempty (S1964HonestCFQuotient l A) := by
  constructor
  · rintro ⟨D⟩
    exact ⟨⟨D.stack⟩, ⟨D.cF, D.honest_signature, D.quotient, D.quotientWitness⟩⟩
  · rintro ⟨⟨stack⟩, ⟨Q⟩⟩
    exact ⟨⟨stack, Q.cF, Q.quotient, Q.quotientWitness, Q.cF_signature⟩⟩

/-- The corrected exact target: the D9 quotient together with *the natural
slice-sheaf stack*, not an arbitrary large stack.  The isStack field is exactly
S2050's first missing at the field F = (S1732A l).F. -/
structure S2093LargeCFDataExact (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve) where
  /-- The natural slice-sheaf prestack over F is an etale stack. -/
  isStack : S2050LargeSheafStackMissing (K := (S1732A l).F)
  /-- The quotient orbicurve C_F. -/
  cF : Iut.HyperbolicOrbicurve (S1732A l).F
  /-- The sign-invariant quotient morphism X_F -> C_F. -/
  quotient : Iut.OrbicurveSignInvariantMorphism A cF
  /-- The bicategorical universal property of the quotient. -/
  quotientWitness : Iut.OrbicurveSignQuotientWitness A quotient
  /-- The honest signature (0;[2,2,2];1) of the quotient. -/
  honest_signature : cF.signature = S1964HonestQuotientSignature

/-- The exact large CFData first missing. -/
def S2093LargeCFFirstMissingExact (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve) : Prop :=
  Nonempty (S2093LargeCFDataExact l A)

/-- **Exact first missing of the corrected D9 target.**  It is the conjunction of
the stack missing and the S1964 honest quotient missing.  The stack half is
equivalently the family descent statement of section 3. -/
theorem S2093LargeCFFirstMissingExact_iff :
    S2093LargeCFFirstMissingExact l A ↔
      S2050LargeSheafStackMissing (K := (S1732A l).F) ∧
        Nonempty (S1964HonestCFQuotient l A) := by
  constructor
  · rintro ⟨D⟩
    exact ⟨D.isStack, ⟨D.cF, D.honest_signature, D.quotient, D.quotientWitness⟩⟩
  · rintro ⟨hstack, ⟨Q⟩⟩
    exact ⟨⟨hstack, Q.cF, Q.quotient, Q.quotientWitness, Q.cF_signature⟩⟩

/-- The same exact first missing with the stack half in etale-family form. -/
theorem S2093LargeCFFirstMissingExact_iff_families :
    S2093LargeCFFirstMissingExact l A ↔
      S2093SheafStackOnEtaleFamilies (S1732A l).F ∧
        Nonempty (S1964HonestCFQuotient l A) := by
  rw [S2093LargeCFFirstMissingExact_iff,
    ← S2093SheafStackOnEtaleFamilies_iff,
    S2093LargeSheafStackMissing_iff_S2050]

/-- Forget the exact stack requirement: exact D9 data gives the old large CFData. -/
def S2093LargeCFDataExact.toOld (D : S2093LargeCFDataExact l A) :
    S2050LargeCFData l A :=
  ⟨⟨S2050LargeSheafPrestack (S1732A l).F, D.isStack⟩, D.cF, D.quotient,
    D.quotientWitness, D.honest_signature⟩

/-- The actual consumer of D9: exact large data gives the S1964 quotient structure. -/
def S2093LargeCFDataExact.toS1964 (D : S2093LargeCFDataExact l A) :
    S1964QuotientStructure l A :=
  ⟨D.cF, D.quotient, D.quotientWitness⟩

/-- The corrected target implies the old first missing. -/
theorem S2093LargeCFFirstMissingExact_implies_old
    (h : S2093LargeCFFirstMissingExact l A) : Nonempty (S2050LargeCFData l A) :=
  h.elim fun D => ⟨D.toOld⟩

/-! ## 5. The old small target: pointwise small models and transport

For the old Cat.{u,u} target one needs, for every test object, a u-small model of
the large slice-sheaf category, *and* a transport of the pseudofunctorial structure
along those models.  The pointwise small-model proposition S2050LargeSheafSmallModel
is rewritten as an explicit forall; the transport is the separate missing input
S2093SmallStackTransport. -/

/-- The pointwise small-model input in forall form (choice is used to pass from a
forall of Nonempty to a Nonempty of a forall). -/
theorem S2093LargeSheafSmallModel_iff_forall :
    S2050LargeSheafSmallModel K ↔
      ∀ U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ,
        Nonempty (S2029SmallModel ((S2050LargeSheafPrestack K).obj U)) := by
  constructor
  · rintro ⟨fam⟩ U
    exact ⟨fam U⟩
  · intro h
    classical
    exact ⟨fun U => (h U).some⟩

/-- The pure transport missing for the old target: a Cat.{u,u}-valued pseudofunctor
whose values are pointwise equivalent to the large slice-sheaf prestack.  The
pseudofunctorial structure along the chosen small models is *not* constructed. -/
def S2093SmallModelTransport (K : Type u) [Field K] : Prop :=
  ∃ Q : Iut.EtaleStackPseudofunctor K,
    ∀ U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ,
      Nonempty (↑(Q.obj U) ≌ ↑((S2050LargeSheafPrestack K).obj U))

/-- The exact transport input for the old target: a u-small *stack* together with
pointwise equivalences to the large prestack.  This is the precise form of
"S2029SmallModel + transport". -/
def S2093SmallStackTransport (K : Type u) [Field K] : Prop :=
  ∃ Q : Iut.EtaleStackPseudofunctor K,
    Q.IsStack (Iut.SchemeOverField.etaleTopology K) ∧
      ∀ U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ,
        Nonempty (↑(Q.obj U) ≌ ↑((S2050LargeSheafPrestack K).obj U))

/-- A small stack transport gives in particular the pure transport data. -/
theorem S2093SmallModelTransport_of_smallStackTransport
    (h : S2093SmallStackTransport K) : S2093SmallModelTransport K := by
  obtain ⟨Q, _hQ, hE⟩ := h
  exact ⟨Q, hE⟩

/-- **The transport input supplies the S2029 pointwise small models.** -/
theorem S2093SmallModelTransport_implies_smallModel
    (h : S2093SmallModelTransport K) : S2050LargeSheafSmallModel K := by
  obtain ⟨Q, hE⟩ := h
  exact ⟨fun U => ⟨Q.obj U, hE U⟩⟩

/-- Consequently the exact transport input supplies S2050's small-model
proposition. -/
theorem S2093SmallStackTransport_implies_smallModel
    (h : S2093SmallStackTransport K) : S2050LargeSheafSmallModel K :=
  S2093SmallModelTransport_implies_smallModel
    (S2093SmallModelTransport_of_smallStackTransport h)

/-- The exact transport input supplies an actual small etale stack. -/
theorem S2093SmallStackTransport_implies_smallStack
    (h : S2093SmallStackTransport K) :
    ∃ Q : Iut.EtaleStackPseudofunctor K,
      Q.IsStack (Iut.SchemeOverField.etaleTopology K) := by
  obtain ⟨Q, hQ, _⟩ := h
  exact ⟨Q, hQ⟩

/-! ## 6. Axiom footprint -/

#print axioms S2093LargeSheafStackMissing_iff_S2029
#print axioms S2093LargeSheafStackMissing_iff_IsStack
#print axioms S2093LargeSheafPrestack_obj
#print axioms S2093LargeSheafStackMissing_iff_decomposition
#print axioms S2093SheafPrestack_iff_presheafHom
#print axioms S2093SchemeEtalePrecoverage_hasIsos
#print axioms S2093SchemeEtalePrecoverage_stableComp
#print axioms S2093SchemeEtalePrecoverage_stableBase
#print axioms S2093EtalePrecoverage_toGrothendieck
#print axioms S2093SheafStackOnEtaleFamilies_of_stack
#print axioms S2093LargeSheafStackMissing_of_etaleFamilies
#print axioms S2093SheafStackOnEtaleFamilies_iff
#print axioms S2093LargeCFData_iff
#print axioms S2093LargeCFFirstMissingExact_iff
#print axioms S2093LargeCFFirstMissingExact_iff_families
#print axioms S2093LargeCFDataExact.toOld
#print axioms S2093LargeCFDataExact.toS1964
#print axioms S2093LargeCFFirstMissingExact_implies_old
#print axioms S2093LargeSheafSmallModel_iff_forall
#print axioms S2093SmallModelTransport_of_smallStackTransport
#print axioms S2093SmallModelTransport_implies_smallModel
#print axioms S2093SmallStackTransport_implies_smallModel
#print axioms S2093SmallStackTransport_implies_smallStack

end LeanFormal.IUT.XiFPaper.S2093D9StackActual
