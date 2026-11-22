import LeanFormal.IUT.IUTIII.Theorem311.SourceFaithfulBoundary
import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteMultiradial
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Ind1: the first quotient compatibility of the Theorem 3.11 output

Reduction pass for the audit obligation `IUT-III.Ind1`
(`Indeterminacy/Ind1.lean`: "Prove the first quotient compatibility from the
constructed output").

## Source location

* IUT III, Theorem 3.11, (i) defines the multiradial representation
  `n,oR_LGP` of the data (a), (b), (c) over the procession of D-prime-strips
  `Prc(n,oD_T)` up to two indeterminacies; the first one,
  (Ind1), consists of "the indeterminacies induced by the automorphisms of the
  procession of D-prime-strips", and the theorem asserts that the
  representation "may be constructed via an algorithm in the procession ...
  that is functorial with respect to isomorphisms of processions of
  D-prime-strips".
* IUT III, Remark 3.11.1, (i) summarizes the construction and singles out the
  functoriality with respect to the permutation symmetries of the etale-picture.
* IUT III, proof of Corollary 3.12, Step (x), reads the indeterminacies as
  describing a "formal quotient" and records that the procession-normalized
  log-volumes are invariant under (Ind1), (Ind2), with (Ind3) becoming an
  inequality from above.
* Essential Logical Structure, §3.10, (Stp2) ("Introduction of (Ind1)")
  describes the same step as a descent to weaker (mono-analytic etale-like)
  input data.

## What is proved here, and at which boundary

The repository does not reconstruct the scheme-theoretic procession or its
automorphism group.  It froze the abstract carrier boundary
`Theorem311Source.Input` with a core `MultiradialKernel.Core Label Choice`
(group laws for `ind1`, `ind2`, `ind3`), the orbit relation
`Ind1Relation I` of the `ind1` action, and the canonical projection
`quotientMap I` to the indeterminacy quotient.

At that boundary this file supplies:

1. the formal quotient of (Ind1) as a `Setoid`, the induced projection, the
   descent of `quotientMap` through it, and the universal property
   (uniqueness) of that descent;
2. functoriality of the formal quotient with respect to maps and equivalences
   that preserve and reflect `Ind1Relation` (the model-level counterpart of
   the functoriality sentence of Theorem 3.11, (i));
3. the output-level clause: for any constructed `Theorem311Output I`, the
   quotient component is the descended image of the Ind1-class of the output
   source, and it is constant along that class;
4. the quotient-level invariants (log-volume, possible image, directed level)
   are constant along `Ind1Relation`-related representatives;
5. a finite-carrier instance over `SourceFiniteMultiradial.core`, including an
   explicit Ind1 step between distinct choices whose formal quotient classes
   agree, so that the compatibility is not vacuous on the finite carrier.

This is a *reduced* (model-level) form of the source statement; the paper's
objects are not reconstructed here, and source faithfulness of the carrier is
not claimed.  The remaining source-facing content is recorded as a card in
`logs/coordination/ind1-reduction-20261016.md`.
-/

namespace LeanFormal.IUT

open MultiradialKernel

universe u v

namespace MultiradialKernel.Core

variable {Label : Type u} {Choice : Type v} [AddGroup Label]

/-- Single-step (Ind1) form of `generatedQuotientMap_eq_of_generated`: the
    canonical projection to the formal quotient absorbs any one `ind1` step. -/
theorem generatedQuotientMap_eq_of_ind1Step (core : Core Label Choice)
    {a b : Choice} (h : Ind1Step core a b) :
    generatedQuotientMap core a = generatedQuotientMap core b :=
  generatedQuotientMap_eq_of_generated core (.ind1 h)

end MultiradialKernel.Core

namespace Theorem311Source

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {Choice' : Type v} [Preorder Choice']

/-! ## The formal quotient of (Ind1) and the descent of the quotient map -/

/-- The setoid of the first indeterminacy: its classes are the orbits of the
    `ind1` action.  This is the index of the "formal quotient" by (Ind1). -/
def Ind1Setoid (I : Input Label Choice) : Setoid Choice where
  r := Ind1Relation I
  iseqv :=
    { refl := ind1_relation_refl I
      symm := fun h => ind1_relation_symm I h
      trans := fun h₁ h₂ => ind1_relation_trans I h₁ h₂ }

/-- The canonical projection to the formal quotient by (Ind1). -/
def ind1QuotientMap (I : Input Label Choice) : Choice → Quotient (Ind1Setoid I) :=
  fun c => Quotient.mk'' c

/-- The `ind1` action is absorbed by the formal quotient projection. -/
theorem ind1QuotientMap_ind1 (I : Input Label Choice) (g : Label) (c : Choice) :
    ind1QuotientMap I (I.core.ind1 g c) = ind1QuotientMap I c :=
  Quotient.sound' ⟨-g, I.core.ind1_inverse g c⟩

/-- The first quotient compatibility as a map out of the formal quotient. -/
def ind1QuotientLift (I : Input Label Choice) :
    Quotient (Ind1Setoid I) → IndeterminacyQuotient I :=
  fun q => q.liftOn' (quotientMap I) (fun _ _ h => quotientMap_respects_ind1 I h)

theorem ind1QuotientLift_mk'' (I : Input Label Choice) (c : Choice) :
    ind1QuotientLift I (Quotient.mk'' c) = quotientMap I c :=
  Quotient.liftOn'_mk'' (quotientMap I)
    (fun _ _ h => quotientMap_respects_ind1 I h) c

@[simp] theorem ind1QuotientLift_mk (I : Input Label Choice) (c : Choice) :
    ind1QuotientLift I (ind1QuotientMap I c) = quotientMap I c :=
  ind1QuotientLift_mk'' I c

/-- Universal property of the descent: any map out of the formal quotient
    that computes `quotientMap` on representatives is the descended map. -/
theorem ind1QuotientLift_unique (I : Input Label Choice)
    (candidate : Quotient (Ind1Setoid I) → IndeterminacyQuotient I)
    (h_candidate : ∀ c, candidate (ind1QuotientMap I c) = quotientMap I c) :
    candidate = ind1QuotientLift I := by
  funext q
  refine Quotient.inductionOn' q ?_
  intro c
  have hc := h_candidate c
  simp only [ind1QuotientMap] at hc
  rw [hc, ind1QuotientLift_mk'']

/-! ## Functoriality with respect to Ind1-class preserving maps -/

/-- Model-level functoriality: a map sending `Ind1Relation`-related choices to
    `Ind1Relation`-related choices induces a map of formal quotients. -/
def ind1QuotientFunctorial (I : Input Label Choice) (I' : Input Label Choice')
    (e : Choice → Choice')
    (he : ∀ ⦃a b : Choice⦄, Ind1Relation I a b → Ind1Relation I' (e a) (e b)) :
    Quotient (Ind1Setoid I) → Quotient (Ind1Setoid I') :=
  Quotient.map' e (fun _ _ h => he h)

@[simp] theorem ind1QuotientFunctorial_mk'' (I : Input Label Choice)
    (I' : Input Label Choice') (e : Choice → Choice')
    (he : ∀ ⦃a b : Choice⦄, Ind1Relation I a b → Ind1Relation I' (e a) (e b))
    (c : Choice) :
    ind1QuotientFunctorial I I' e he (Quotient.mk'' c) =
      Quotient.mk'' (e c) :=
  Quotient.map'_mk'' e (fun _ _ h => he h) c

@[simp] theorem ind1QuotientFunctorial_mk (I : Input Label Choice)
    (I' : Input Label Choice') (e : Choice → Choice')
    (he : ∀ ⦃a b : Choice⦄, Ind1Relation I a b → Ind1Relation I' (e a) (e b))
    (c : Choice) :
    ind1QuotientFunctorial I I' e he (ind1QuotientMap I c) =
      ind1QuotientMap I' (e c) :=
  ind1QuotientFunctorial_mk'' I I' e he c

/-- An equivalence of carriers that preserves and reflects `Ind1Relation`
    induces an equivalence of the corresponding formal quotients: the
    model-level counterpart of functoriality with respect to isomorphisms of
    processions. -/
def ind1QuotientEquivOfEquiv (I : Input Label Choice) (I' : Input Label Choice')
    (e : Choice ≃ Choice')
    (he : ∀ a b : Choice, Ind1Relation I a b ↔ Ind1Relation I' (e a) (e b)) :
    Quotient (Ind1Setoid I) ≃ Quotient (Ind1Setoid I') where
  toFun := ind1QuotientFunctorial I I' e (fun a b h => (he a b).mp h)
  invFun := ind1QuotientFunctorial I' I e.symm
    (fun a b h => (he (e.symm a) (e.symm b)).mpr (by simpa using h))
  left_inv := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro c
    simp
  right_inv := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro c
    simp

@[simp] theorem ind1QuotientEquivOfEquiv_mk'' (I : Input Label Choice)
    (I' : Input Label Choice') (e : Choice ≃ Choice')
    (he : ∀ a b : Choice, Ind1Relation I a b ↔ Ind1Relation I' (e a) (e b))
    (c : Choice) :
    ind1QuotientEquivOfEquiv I I' e he (Quotient.mk'' c) =
      Quotient.mk'' (e c) :=
  ind1QuotientFunctorial_mk'' I I' e (fun a b h => (he a b).mp h) c

/-! ## The constructed output -/

/-- The first quotient compatibility extracted from a constructed output:
    `Theorem311Output` carries the descent law as its field `ind1_quotient`. -/
theorem ind1_quotient_eq_from_output (I : Input Label Choice)
    (O : Theorem311Output I) {a b : Choice}
    (h : Ind1Relation I a b) : quotientMap I a = quotientMap I b :=
  O.ind1_quotient h

/-- The output quotient is the descended image of the Ind1-class of the output
    source. -/
theorem output_quotient_eq_ind1QuotientLift (I : Input Label Choice)
    (O : Theorem311Output I) :
    O.quotient = ind1QuotientLift I (ind1QuotientMap I O.source) := by
  rw [O.quotient_eq, ind1QuotientLift_mk]

/-- The output quotient is constant on the Ind1-class of the output source. -/
theorem output_quotient_eq_of_ind1_source (I : Input Label Choice)
    (O : Theorem311Output I) {b : Choice}
    (h : Ind1Relation I O.source b) : O.quotient = quotientMap I b := by
  rw [O.quotient_eq]
  exact quotientMap_respects_ind1 I h

/-- The output log-volume is an Ind1 invariant through the output quotient. -/
theorem output_quotientVolume_eq_of_ind1_source (I : Input Label Choice)
    (O : Theorem311Output I) {b : Choice} (h : Ind1Relation I O.source b) :
    quotientVolume I O.quotient = quotientVolume I (quotientMap I b) := by
  rw [output_quotient_eq_of_ind1_source I O h]

/-! ## Quotient-level invariants along Ind1-related representatives -/

theorem ind1_quotientImage_eq (I : Input Label Choice) {a b : Choice}
    (h : Ind1Relation I a b) :
    quotientImage I (quotientMap I a) = quotientImage I (quotientMap I b) := by
  rw [quotientMap_respects_ind1 I h]

theorem ind1_quotientVolume_eq (I : Input Label Choice) {a b : Choice}
    (h : Ind1Relation I a b) :
    quotientVolume I (quotientMap I a) = quotientVolume I (quotientMap I b) := by
  rw [quotientMap_respects_ind1 I h]

theorem ind1_quotientLevel_eq (I : Input Label Choice) {a b : Choice}
    (h : Ind1Relation I a b) :
    quotientLevel I (quotientMap I a) = quotientLevel I (quotientMap I b) := by
  rw [quotientMap_respects_ind1 I h]

/-! ## The named conditional interface -/

/-- Carrier-plus-card form of the first quotient compatibility: a formal
    quotient of the choice carrier together with the descent of the
    indeterminacy quotient through it.  The canonical instance is
    `ind1DescentDataCanonical`, so the card is inhabited for every carrier. -/
structure Ind1DescentData (I : Input Label Choice) where
  formalQuotient : Type v
  project : Choice → formalQuotient
  descend : formalQuotient → IndeterminacyQuotient I
  descend_project : ∀ c, descend (project c) = quotientMap I c
  project_ind1 : ∀ {a b}, Ind1Relation I a b → project a = project b

/-- Assembly: every carrier satisfies the card through its formal quotient. -/
def ind1DescentDataCanonical (I : Input Label Choice) : Ind1DescentData I where
  formalQuotient := Quotient (Ind1Setoid I)
  project := ind1QuotientMap I
  descend := ind1QuotientLift I
  descend_project := ind1QuotientLift_mk I
  project_ind1 := fun h => Quotient.sound' h

/-- Consumer extraction from the card: the first quotient compatibility. -/
theorem ind1DescentData_descends (I : Input Label Choice) (D : Ind1DescentData I)
    {a b : Choice} (h : Ind1Relation I a b) : quotientMap I a = quotientMap I b := by
  rw [← D.descend_project a, ← D.descend_project b, D.project_ind1 h]

end Theorem311Source

namespace SourceFiniteMultiradial

open MultiradialKernel
open MultiradialKernel.Core
open ConcreteFiniteTheorem311

/-! ## A non-vacuous finite-carrier instance -/

/-- The finite label `ZMod l.value` is nontrivial: `1 != 0`. -/
theorem finiteLabel_one_ne_zero (l : PrimeGeFive) :
    (1 : ConcreteFiniteTheorem311.finiteLabel l) ≠ 0 := by
  intro h
  have hval : (1 : ConcreteFiniteTheorem311.finiteLabel l).val = 0 :=
    (congrArg ZMod.val h).trans ZMod.val_zero
  have hne : l.value ≠ 1 := by
    have h5 := l.ge_five
    omega
  rw [ZMod.val_one'' (n := l.value) hne] at hval
  exact Nat.one_ne_zero hval

/-- Single-step (Ind1) quotient compatibility on the finite carrier. -/
theorem ind1Step_generatedQuotientMap_eq {l : PrimeGeFive}
    {a b : ProcessionChoice l} (h : Core.Ind1Step (core l) a b) :
    Core.generatedQuotientMap (core l) a = Core.generatedQuotientMap (core l) b :=
  Core.generatedQuotientMap_eq_of_ind1Step (core l) h

/-- The finite carrier has nontrivial Ind1 steps: from every choice there is a
    distinct choice related to it by an `ind1` step. -/
theorem ind1Step_nontrivial (l : PrimeGeFive) (a : ProcessionChoice l) :
    ∃ b : ProcessionChoice l, Core.Ind1Step (core l) a b ∧ b ≠ a := by
  refine ⟨(core l).ind1 1 a, ⟨1, rfl⟩, ?_⟩
  intro h
  have hlabel : (1 : ConcreteFiniteTheorem311.finiteLabel l) + a.processionLabel =
      a.processionLabel := by
    have h' : (ProcessionChoice.ind1Act 1 a).processionLabel = a.processionLabel :=
      congrArg ProcessionChoice.processionLabel h
    simpa using h'
  have h10 : (1 : ConcreteFiniteTheorem311.finiteLabel l) = 0 := by
    have h' := congrArg (fun y : ConcreteFiniteTheorem311.finiteLabel l =>
      y + (-a.processionLabel)) hlabel
    simpa [add_assoc] using h'
  exact finiteLabel_one_ne_zero l h10

/-- Strict identification: there are distinct choices related by an `ind1`
    step whose formal quotient classes agree. -/
theorem ind1Step_strict_identification (l : PrimeGeFive) (a : ProcessionChoice l) :
    ∃ b : ProcessionChoice l,
      Core.Ind1Step (core l) a b ∧ b ≠ a ∧
        Core.generatedQuotientMap (core l) a =
          Core.generatedQuotientMap (core l) b := by
  obtain ⟨b, hstep, hne⟩ := ind1Step_nontrivial l a
  exact ⟨b, hstep, hne, ind1Step_generatedQuotientMap_eq hstep⟩

/-- Quotient compatibility of the constructed finite multiradial output: along
    a horizontal route the algorithm output target has the same formal
    quotient class as its source. -/
theorem routeOutput_horizontal_target_quotient_eq (l : PrimeGeFive)
    (source : ProcessionChoice l)
    (route : List (RouteStep (ConcreteFiniteTheorem311.finiteLabel l)))
    (hroute : ∀ step ∈ route, horizontal step) :
    Core.generatedQuotientMap (core l)
        (MultiradialKernel.Output.target (routeOutput l source route)) =
      Core.generatedQuotientMap (core l) source := by
  rw [routeOutput_target]
  exact (Core.generatedQuotientMap_eq_of_generated (core l)
    (generated_of_horizontal_route (core l) route hroute source)).symm

end SourceFiniteMultiradial

end LeanFormal.IUT
