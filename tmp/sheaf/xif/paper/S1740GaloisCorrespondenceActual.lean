/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual
import Mathlib.CategoryTheory.Galois.Equivalence
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Iut.Foundations.SourceContinuousAnabelioid

/-!
# S1740: the Galois correspondence for the actual D6 orbicurve

This file constructs, from an actual finite-etale fiber functor on the S1726
orbicurve, the Galois correspondence with finite sets acted on by the orbifold
fundamental group.  It does not postulate such a fiber functor: the input is
exactly Mathlib's PreGaloisCategory.FiberFunctor together with the certificate
PreGaloisCategory.IsFundamentalGroup that the chosen group is the fundamental
group of that fiber functor.

The main construction is

  S1740ContEquivalence D : OrbicurveFiniteEtaleCover X ≌ ContAction FintypeCat G

for an actual datum D : Iut.OrbicurveEtaleFundamentalGroup X G.  This is the
categorical Galois correspondence: the covers are equivalent to finite discrete
G-sets with continuous action (Mochizuki's B(G)).

The candidate functor into the unrestricted finite-action category

  S1740FunctorToAction D : OrbicurveFiniteEtaleCover X ⥤ Action FintypeCat G

is also constructed and is proved fully faithful.  Its object is the literal
fiber D.fiber.obj cover, and its action is the actual D.action cover
(S1740FunctorToAction_smul).  It becomes an equivalence as soon as every
finite G-set carries a continuous action; this sufficient condition is exposed
as the missing input S1740AllActionsContinuous G, not assumed.  The literal
essential-surjectivity condition of the candidate is isolated as
S1740CandidateEssSurj.

For the actual D6 datum of S1726,

  D : Iut.OrbicurveFundamentalGroupData S1726Orbicurve (AbsoluteGaloisProfinite F'),

the arithmetic group D.arithmeticGroup is the group of the Galois
correspondence (S1740D6ContEquivalence).  The literal group asked for in the
task, AbsoluteGaloisProfinite F', receives a surjection from it.  Passing to
that group requires a continuous isomorphism D.arithmeticGroup ≃ₜ* G plus
S1740AllActionsContinuous G; both are exposed as the exact first missing data
in S1740D6BaseWitness, and the conditional equivalence is
S1740D6BaseActionEquivalence.

## Mathlib inputs used

* PreGaloisCategory.functorToContAction and its IsEquivalence instance
  (Mathlib.CategoryTheory.Galois.Equivalence): a fiber functor induces an
  equivalence with finite continuous Aut F-sets.
* PreGaloisCategory.toAutMulEquiv and
  PreGaloisCategory.toAutMulEquiv_isHomeomorph
  (Mathlib.CategoryTheory.Galois.IsFundamentalgroup): a certified
  fundamental group is continuously isomorphic to Aut F.
* ContAction.resEquiv (Mathlib.CategoryTheory.Action.Continuous):
  transport continuous actions along a continuous group isomorphism.
* Iut.continuousActionInclusion and Iut.continuousAction_preGaloisCategory
  (Iut.Foundations.SourceContinuousAnabelioid): the full inclusion of
  continuous finite actions into all finite actions.
* FintypeCat.Action.isConnected_iff_transitive and
  FintypeCat.Action.isConnected_of_transitive
  (Mathlib.CategoryTheory.Galois.Examples): connected finite G-sets are
  exactly the nonempty transitive G-sets.
* PreGaloisCategory.isPretransitive_of_surjective
  (Mathlib.CategoryTheory.Galois.IsFundamentalgroup): the fiber of a
  connected object is a transitive set.

No sorry, axiom, admit, Shrink, ULift or PUnit substitute is used.  The only
inputs are the actual orbicurve of S1726 and the actual fiber-functor datum.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

open scoped FintypeCatDiscrete

namespace LeanFormal.IUT.XiFPaper.S1740GaloisCorrespondenceActual

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual

/-! ## 0. The actual D6 source objects -/

/-- The actual base field F' of S1720/S1726. -/
abbrev S1740BaseField : Type := S1720Field

/-- The task's group: the absolute Galois group of F', as a profinite group. -/
abbrev S1740Galois : ProfiniteGrp.{0} :=
  Iut.AbsoluteGaloisProfinite S1720Field

/-- The actual D6 hyperbolic orbicurve of S1726. -/
abbrev S1740Orbicurve : Iut.HyperbolicOrbicurve S1720Field :=
  S1726Orbicurve

/-- The actual finite-etale cover category carrier of the S1726 orbicurve. -/
abbrev S1740Cover : Type 1 :=
  Iut.OrbicurveFiniteEtaleCover S1740Orbicurve

/-- The exact D6 source datum over the absolute Galois group: the certified
orbifold fundamental-group data of S1726. -/
abbrev S1740D6Data : Type 1 :=
  Iut.OrbicurveFundamentalGroupData S1740Orbicurve S1740Galois

/-- The arithmetic group of a D6 datum. -/
abbrev S1740D6Arithmetic (D : S1740D6Data) : ProfiniteGrp.{0} :=
  D.arithmeticGroup

/-- The actual fiber-functor datum of a D6 datum at its arithmetic group. -/
abbrev S1740D6FiberFunctorData (D : S1740D6Data) :
    Iut.OrbicurveEtaleFundamentalGroup S1740Orbicurve D.arithmeticGroup :=
  D.arithmetic

/-! ## 1. The continuous-action Galois correspondence from a fiber functor -/

variable (G : ProfiniteGrp.{0})

/-- The continuous isomorphism between the certified fundamental group and the
automorphism group of the actual fiber functor. -/
noncomputable def S1740ToAutContinuous
    (D : Iut.OrbicurveEtaleFundamentalGroup S1740Orbicurve G) :
    letI := D.coverCategory
    G ≃ₜ* Aut D.fiber := by
  letI := D.coverCategory
  letI := D.galoisCategory
  letI := D.fiberFunctor
  letI : ∀ cover, MulAction G (D.fiber.obj cover) := D.action
  letI : PreGaloisCategory.IsFundamentalGroup D.fiber G := D.isFundamentalGroup
  let e : G ≃* Aut D.fiber := PreGaloisCategory.toAutMulEquiv D.fiber G
  let h : IsHomeomorph e :=
    PreGaloisCategory.toAutMulEquiv_isHomeomorph D.fiber G
  exact ContinuousMulEquiv.mk' (h.homeomorph e) (fun x y => e.map_mul x y)

/-- **The Galois correspondence**, conditional only on the actual fiber-functor
datum of the orbicurve: finite-etale covers of the S1726 orbicurve are
equivalent to finite discrete sets with a continuous action of the certified
fundamental group G. -/
noncomputable def S1740ContEquivalence
    (D : Iut.OrbicurveEtaleFundamentalGroup S1740Orbicurve G) :
    letI := D.coverCategory
    S1740Cover ≌ ContAction FintypeCat.{0} G := by
  letI := D.coverCategory
  letI := D.galoisCategory
  letI := D.fiberFunctor
  letI : ∀ cover, MulAction G (D.fiber.obj cover) := D.action
  letI : PreGaloisCategory.IsFundamentalGroup D.fiber G := D.isFundamentalGroup
  exact (PreGaloisCategory.functorToContAction D.fiber).asEquivalence.trans
    (ContAction.resEquiv FintypeCat.{0} (S1740ToAutContinuous G D))

/-- The candidate functor to the unrestricted category of finite G-actions.
Its values are the actual fibers, with the actual action. -/
noncomputable def S1740FunctorToAction
    (D : Iut.OrbicurveEtaleFundamentalGroup S1740Orbicurve G) :
    letI := D.coverCategory
    S1740Cover ⥤ Action FintypeCat.{0} G := by
  letI := D.coverCategory
  exact (S1740ContEquivalence G D).functor ⋙
    Iut.continuousActionInclusion G

/-- The candidate functor is full: every morphism of finite actions between
fibers comes from a morphism of covers. -/
theorem S1740FunctorToAction_full
    (D : Iut.OrbicurveEtaleFundamentalGroup S1740Orbicurve G) :
    letI := D.coverCategory
    (S1740FunctorToAction G D).Full := by
  letI := D.coverCategory
  change ((S1740ContEquivalence G D).functor ⋙
    Iut.continuousActionInclusion G).Full
  infer_instance

/-- The candidate functor is faithful. -/
theorem S1740FunctorToAction_faithful
    (D : Iut.OrbicurveEtaleFundamentalGroup S1740Orbicurve G) :
    letI := D.coverCategory
    (S1740FunctorToAction G D).Faithful := by
  letI := D.coverCategory
  change ((S1740ContEquivalence G D).functor ⋙
    Iut.continuousActionInclusion G).Faithful
  infer_instance

/-- **Fiber = underlying finite set**: the underlying finite set of the action
attached to a cover is literally the fiber functor's value on that cover. -/
theorem S1740FunctorToAction_obj_V
    (D : Iut.OrbicurveEtaleFundamentalGroup S1740Orbicurve G)
    (cover : S1740Cover) :
    letI := D.coverCategory
    ((S1740FunctorToAction G D).obj cover).V = D.fiber.obj cover := by
  letI := D.coverCategory
  rfl

/-- **Fiber action**: the action on the underlying finite set of a cover is the
actual action stored in the fiber-functor datum (not an arbitrary action). -/
theorem S1740FunctorToAction_smul
    (D : Iut.OrbicurveEtaleFundamentalGroup S1740Orbicurve G) :
    letI := D.coverCategory
    letI := D.galoisCategory
    letI := D.fiberFunctor
    ∀ (cover : S1740Cover),
      letI := D.action cover
      ∀ (g : G) (x : (D.fiber.obj cover).obj),
        (((S1740FunctorToAction G D).obj cover).ρ g).hom x = g • x := by
  letI := D.coverCategory
  letI := D.galoisCategory
  letI := D.fiberFunctor
  letI : ∀ cover, MulAction G (D.fiber.obj cover) := D.action
  letI : PreGaloisCategory.IsFundamentalGroup D.fiber G := D.isFundamentalGroup
  intro cover g x
  change (PreGaloisCategory.toAutMulEquiv D.fiber G g).hom.app cover x = g • x
  rw [PreGaloisCategory.toAutMulEquiv_apply]
  exact PreGaloisCategory.toAut_hom_app_apply D.fiber g x

/-! ## 2. The exact missing condition for the unrestricted action category -/

/-- The precise extra condition needed to upgrade the fully faithful candidate
to an equivalence with all finite G-sets: every finite G-set carries the
continuous action.  Equivalently (for a profinite group), every finite-index
subgroup is open.  This is not asserted. -/
def S1740AllActionsContinuous (G : ProfiniteGrp.{0}) : Prop :=
  ∀ A : Action FintypeCat.{0} G, Action.IsContinuous A

/-- The candidate's essential-surjectivity condition, isolated exactly. -/
def S1740CandidateEssSurj
    (D : Iut.OrbicurveEtaleFundamentalGroup S1740Orbicurve G) : Prop :=
  letI := D.coverCategory
  (S1740FunctorToAction G D).EssSurj

/-- If every finite action is continuous, the full inclusion is essentially
surjective. -/
theorem S1740ContinuousActionInclusion_essSurj_of_allContinuous
    (h : S1740AllActionsContinuous G) :
    (Iut.continuousActionInclusion G).EssSurj :=
  ⟨fun A => ⟨⟨A, h A⟩, ⟨Iso.refl _⟩⟩⟩

/-- If E : C ≌ ContAction FintypeCat G and every finite action is continuous,
then the composite to all finite actions is essentially surjective. -/
theorem S1740EssSurjOfContEquivalenceAllContinuous
    [Category.{0, 1} S1740Cover]
    (E : S1740Cover ≌ ContAction FintypeCat.{0} G)
    (h : S1740AllActionsContinuous G) :
    (E.functor ⋙ Iut.continuousActionInclusion G).EssSurj := by
  refine ⟨fun A => ?_⟩
  obtain ⟨S, ⟨eS⟩⟩ :=
    (S1740ContinuousActionInclusion_essSurj_of_allContinuous G h).mem_essImage A
  let cover : S1740Cover := E.inverse.obj S
  exact ⟨cover, ⟨
    (Iut.continuousActionInclusion G).mapIso (E.counitIso.app S) ≪≫ eS⟩⟩

/-- The candidate functor is essentially surjective as soon as every finite
action is continuous. -/
theorem S1740FunctorToAction_essSurj_of_allContinuous
    (D : Iut.OrbicurveEtaleFundamentalGroup S1740Orbicurve G)
    (h : S1740AllActionsContinuous G) :
    S1740CandidateEssSurj G D := by
  letI := D.coverCategory
  change ((S1740ContEquivalence G D).functor ⋙
    Iut.continuousActionInclusion G).EssSurj
  exact S1740EssSurjOfContEquivalenceAllContinuous G
    (S1740ContEquivalence G D) h

/-- From any continuous-action equivalence and the all-continuity condition,
build the equivalence with all finite actions. -/
noncomputable def S1740EquivalenceOfContEquivalenceAllContinuous
    [Category.{0, 1} S1740Cover]
    (E : S1740Cover ≌ ContAction FintypeCat.{0} G)
    (h : S1740AllActionsContinuous G) :
    S1740Cover ≌ Action FintypeCat.{0} G := by
  let F := E.functor ⋙ Iut.continuousActionInclusion G
  haveI : F.Full := by
    change (E.functor ⋙ Iut.continuousActionInclusion G).Full
    infer_instance
  haveI : F.Faithful := by
    change (E.functor ⋙ Iut.continuousActionInclusion G).Faithful
    infer_instance
  haveI : F.EssSurj :=
    S1740EssSurjOfContEquivalenceAllContinuous G E h
  letI : F.IsEquivalence :=
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }
  exact F.asEquivalence

/-- The conditional equivalence with the unrestricted finite-action category:
it uses exactly the missing condition S1740AllActionsContinuous G. -/
noncomputable def S1740ActionEquivalenceOfAllContinuous
    (D : Iut.OrbicurveEtaleFundamentalGroup S1740Orbicurve G)
    (h : S1740AllActionsContinuous G) :
    letI := D.coverCategory
    S1740Cover ≌ Action FintypeCat.{0} G := by
  letI := D.coverCategory
  exact S1740EquivalenceOfContEquivalenceAllContinuous G
    (S1740ContEquivalence G D) h

/-! ## 3. Connected covers and transitive actions -/

/-- Mathlib's connectedness/transitivity theorem for finite G-sets.  This is
the action-side half of the Galois correspondence. -/
theorem S1740Action_isConnected_iff_transitive
    (A : Action FintypeCat.{0} G) [Nonempty A.V.obj] :
    PreGaloisCategory.IsConnected A ↔
      MulAction.IsPretransitive G A.V.obj :=
  FintypeCat.Action.isConnected_iff_transitive G A

/-- The reverse implication, in the form used for finite actions. -/
theorem S1740Action_isConnected_of_transitive
    (A : Action FintypeCat.{0} G) [Nonempty A.V.obj]
    [MulAction.IsPretransitive G A.V.obj] :
    PreGaloisCategory.IsConnected A :=
  FintypeCat.Action.isConnected_of_transitive G A.V

/-- Connected covers have transitive fibers.  This is the cover-side half and is
proved directly from the certified fundamental-group structure. -/
theorem S1740Cover_connected_imp_transitive
    (D : Iut.OrbicurveEtaleFundamentalGroup S1740Orbicurve G) :
    letI := D.coverCategory
    letI := D.galoisCategory
    letI := D.fiberFunctor
    letI : ∀ cover, MulAction G (D.fiber.obj cover) := D.action
    ∀ (cover : S1740Cover), PreGaloisCategory.IsConnected cover →
      MulAction.IsPretransitive G (D.fiber.obj cover).obj := by
  letI := D.coverCategory
  letI := D.galoisCategory
  letI := D.fiberFunctor
  letI : ∀ cover, MulAction G (D.fiber.obj cover) := D.action
  letI : PreGaloisCategory.IsFundamentalGroup D.fiber G := D.isFundamentalGroup
  intro cover hcover
  haveI : PreGaloisCategory.IsConnected cover := hcover
  exact PreGaloisCategory.isPretransitive_of_surjective D.fiber G
    (PreGaloisCategory.toAut_bijective D.fiber G).surjective cover

/-- The continuous-action connectedness theorem from
SourceContinuousAnabelioid: for continuous finite G-sets, connected objects
have transitive underlying actions. -/
theorem S1740ContAction_connected_imp_transitive
    (X : ContAction FintypeCat.{0} G) [PreGaloisCategory.IsConnected X] :
    MulAction.IsPretransitive G X.obj.V.obj :=
  Iut.continuousAction_pretransitive_of_isConnected G X

/-! ## 4. The actual D6 orbicurve: arithmetic and base-group targets -/

/-- **The actual Galois correspondence for the S1726 D6 data**: covers of the
actual orbicurve are equivalent to finite continuous sets acted on by the
arithmetic orbifold fundamental group of the D6 datum. -/
noncomputable def S1740D6ContEquivalence (D : S1740D6Data) :
    letI := D.arithmetic.coverCategory
    S1740Cover ≌ ContAction FintypeCat.{0} D.arithmeticGroup :=
  S1740ContEquivalence D.arithmeticGroup D.arithmetic

/-- The candidate functor for the D6 arithmetic group. -/
noncomputable def S1740D6FunctorToAction (D : S1740D6Data) :
    letI := D.arithmetic.coverCategory
    S1740Cover ⥤ Action FintypeCat.{0} D.arithmeticGroup :=
  S1740FunctorToAction D.arithmeticGroup D.arithmetic

/-- Fiber/action identification for the D6 arithmetic candidate. -/
theorem S1740D6FunctorToAction_obj_V (D : S1740D6Data) (cover : S1740Cover) :
    letI := D.arithmetic.coverCategory
    ((S1740D6FunctorToAction D).obj cover).V =
      D.arithmetic.fiber.obj cover := by
  letI := D.arithmetic.coverCategory
  rfl

/-- The exact first missing data for comparing the D6 arithmetic fundamental
group with the task's absolute Galois group, and for upgrading continuous
actions to all finite actions.

The first field is the comparison of the algebraic fundamental group with the
Galois group; the actual D6 datum only supplies a surjection
D.arithmeticGroup → AbsoluteGaloisProfinite F' with the geometric kernel.
The second field is S1740AllActionsContinuous. -/
structure S1740D6BaseWitness (D : S1740D6Data) where
  /-- Continuous isomorphism identifying the arithmetic group with the absolute
  Galois group of F'.  This is the missing identification; the D6 datum only
  supplies a surjection. -/
  arithmeticIso : D.arithmeticGroup ≃ₜ* S1740Galois
  /-- Every finite G-set is continuous; equivalently every finite-index
  subgroup of the absolute Galois group is open. -/
  allActionsContinuous : S1740AllActionsContinuous S1740Galois

/-- Conditional Galois correspondence at the task's literal group
AbsoluteGaloisProfinite F', using the exact missing witness. -/
noncomputable def S1740D6BaseContEquivalence
    (D : S1740D6Data) (W : S1740D6BaseWitness D) :
    letI := D.arithmetic.coverCategory
    S1740Cover ≌ ContAction FintypeCat.{0} S1740Galois := by
  letI := D.arithmetic.coverCategory
  exact (S1740D6ContEquivalence D).trans
    (ContAction.resEquiv FintypeCat.{0} W.arithmeticIso).symm

/-- Conditional equivalence with the unrestricted finite-action category at the
task's literal group. -/
noncomputable def S1740D6BaseActionEquivalence
    (D : S1740D6Data) (W : S1740D6BaseWitness D) :
    letI := D.arithmetic.coverCategory
    S1740Cover ≌ Action FintypeCat.{0} S1740Galois := by
  letI := D.arithmetic.coverCategory
  exact S1740EquivalenceOfContEquivalenceAllContinuous S1740Galois
    (S1740D6BaseContEquivalence D W) W.allActionsContinuous

/-- The unconditional candidate functor into all finite
AbsoluteGaloisProfinite F'-sets, from the D6 arithmetic datum and the exact
missing group comparison.  Its essential image is the continuous actions. -/
noncomputable def S1740D6BaseFunctorToAction
    (D : S1740D6Data) (W : S1740D6BaseWitness D) :
    letI := D.arithmetic.coverCategory
    S1740Cover ⥤ Action FintypeCat.{0} S1740Galois := by
  letI := D.arithmetic.coverCategory
  exact (S1740D6BaseContEquivalence D W).functor ⋙
    Iut.continuousActionInclusion S1740Galois

/-- Fiber/underlying-set identification for the base-group candidate. -/
theorem S1740D6BaseFunctorToAction_obj_V
    (D : S1740D6Data) (W : S1740D6BaseWitness D) (cover : S1740Cover) :
    letI := D.arithmetic.coverCategory
    ((S1740D6BaseFunctorToAction D W).obj cover).V =
      D.arithmetic.fiber.obj cover := by
  letI := D.arithmetic.coverCategory
  change ((S1740D6ContEquivalence D).functor.obj cover).obj.V =
    D.arithmetic.fiber.obj cover
  exact S1740D6FunctorToAction_obj_V D cover

/-- The D6 datum's projection to the absolute Galois group. -/
theorem S1740D6_projection_surjective (D : S1740D6Data) :
    Function.Surjective D.projection :=
  D.projection_surjective

/-- The D6 exact missing surface: the comparison of the arithmetic group with
AbsoluteGaloisProfinite F' plus the all-continuity condition. -/
abbrev S1740D6BaseFirstMissing (D : S1740D6Data) : Type :=
  S1740D6BaseWitness D

/-! ## 5. Mathlib theorem inventory -/

#check PreGaloisCategory.functorToContAction
#check PreGaloisCategory.toAutMulEquiv
#check PreGaloisCategory.toAutMulEquiv_isHomeomorph
#check ContAction.resEquiv
#check Iut.continuousActionInclusion
#check Iut.continuousAction_preGaloisCategory
#check Iut.continuousAction_isFundamentalGroup
#check FintypeCat.Action.isConnected_iff_transitive
#check FintypeCat.Action.isConnected_of_transitive
#check PreGaloisCategory.isPretransitive_of_surjective
#check Iut.continuousAction_pretransitive_of_isConnected

/-! ## 6. Axiom footprint -/

#print axioms S1740ToAutContinuous
#print axioms S1740ContEquivalence
#print axioms S1740FunctorToAction
#print axioms S1740FunctorToAction_full
#print axioms S1740FunctorToAction_faithful
#print axioms S1740FunctorToAction_obj_V
#print axioms S1740FunctorToAction_smul
#print axioms S1740ContinuousActionInclusion_essSurj_of_allContinuous
#print axioms S1740EssSurjOfContEquivalenceAllContinuous
#print axioms S1740FunctorToAction_essSurj_of_allContinuous
#print axioms S1740EquivalenceOfContEquivalenceAllContinuous
#print axioms S1740ActionEquivalenceOfAllContinuous
#print axioms S1740Action_isConnected_iff_transitive
#print axioms S1740Action_isConnected_of_transitive
#print axioms S1740Cover_connected_imp_transitive
#print axioms S1740ContAction_connected_imp_transitive
#print axioms S1740D6ContEquivalence
#print axioms S1740D6FunctorToAction
#print axioms S1740D6FunctorToAction_obj_V
#print axioms S1740D6BaseContEquivalence
#print axioms S1740D6BaseActionEquivalence
#print axioms S1740D6BaseFunctorToAction
#print axioms S1740D6BaseFunctorToAction_obj_V
#print axioms S1740D6_projection_surjective

end LeanFormal.IUT.XiFPaper.S1740GaloisCorrespondenceActual

end
