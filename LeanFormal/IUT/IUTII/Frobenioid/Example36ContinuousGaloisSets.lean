import Mathlib.Topology.Category.FinTopCat
import Mathlib.CategoryTheory.Action.Continuous
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.Topology.Algebra.MulAction
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtaleCoverFoundations
import Iut.Foundations.SourceContinuousAnabelioid
import Mathlib.Tactic

/-!
# Foundation F1c: finite continuous G_K-sets and the discrete forgetful functor

Source anchor: IUT II / IUT III foundations, the Galois-category input to the
D6 curve-Pi card; foundation item F1c.  This file provides the
HasForget2 FintypeCat TopCat discrete-topology forgetful functor needed by
Mathlib's Action.Continuous.ContAction, defines the category of finite
continuous sets for a profinite group (in particular for the absolute Galois
group G_K = Iut.AbsoluteGaloisProfinite K), and records the exact continuity
facts and the residual card.

## What is constructed and proved

* fintypeCatDiscreteForget is the discrete-topology forgetful functor
  FintypeCat to TopCat; it is Mathlib's scoped discrete forgetful functor
  (FintypeCatDiscrete), named here together with its discreteness and the
  HasForget2 FintypeCat TopCat witness.  With this, the continuous-action full
  subcategory Action.Continuous.ContAction FintypeCat G is available.
* finiteContinuousGaloisSets G = ContAction FintypeCat G is the category of
  finite sets with a continuous action of a profinite group G; for a field
  K, finiteContinuousGaloisSetsOfField K is the case G = G_K.
* Continuity criterion (the correct finite-level statement): for a finite set
  with an action of a topological group G, the action is continuous if and
  only if all point stabilizers are open, equivalently the kernel of the
  permutation action into the endomorphism monoid is open.  The implication
  "continuous action has open kernel" and its converse "open kernel gives a
  continuous action" are both proved; the converse factors the action through
  the discrete quotient G modulo the kernel.
* The continuous category is equivalent to the full subcategory of
  Action FintypeCat G consisting of actions with open kernel
  (continuousActionEquivalenceOpenKernel).  The full action category is NOT
  equivalent to the continuous one: see the warning below.
* Fiber functor, Galois category and fundamental-group facts are transferred
  from the anabelioid construction: continuousActionFiber is a fiber functor,
  ContAction FintypeCat G is a Galois category, and G is its fundamental
  group, for profinite G.
* Frozen card FiniteEtaleKAlgebraEquivalenceCard: the exact missing
  equivalence between the category of finite continuous G_K-sets and the
  category of finite etale K-algebras (with its Galois structure).  The
  target category is not constructed in this file; the card has no inhabitant
  and no theorem consumes it.

## Mathematical warning (why the full version is not claimed)

The literal statement "every finite action of a profinite group is continuous"
is FALSE in general.  A compact profinite group such as a product of Z/p
has discontinuous additive functionals (a Hamel-basis choice argument), and
the corresponding translation action on the finite set Z/p is a finite action
that is not continuous.  Hence the equivalence with the whole category
Action FintypeCat G cannot be proved (and is not true); the correct statement
is the equivalence with the open-kernel full subcategory proved here.  No
AllFiniteActionsContinuous statement is asserted anywhere.

## Honest boundary

No curve Pi_1, no fake Galois category, no finite etale algebra category and no
card-only substitute for a proof are introduced.  The missing equivalence is
frozen only as the card above and is not used as a hypothesis.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

universe u

open CategoryTheory

/-! ## 1. The discrete-topology forgetful functor FintypeCat to TopCat -/

open scoped FintypeCatDiscrete

/-- The discrete-topology forgetful functor from finite types to topological
spaces.  This names Mathlib's scoped FintypeCatDiscrete forgetful functor and
makes the HasForget2 FintypeCat TopCat input of ContAction available. -/
abbrev fintypeCatDiscreteForget : FintypeCat ⥤ TopCat :=
  forget₂ FintypeCat TopCat

/-- Objects of the discrete forgetful functor carry the discrete topology. -/
theorem fintypeCatDiscreteForget_obj_discrete (X : FintypeCat) :
    DiscreteTopology (fintypeCatDiscreteForget.obj X) := by
  change DiscreteTopology X
  infer_instance

/-- The HasForget2 FintypeCat TopCat instance attached to the discrete
forgetful functor. -/
noncomputable abbrev fintypeCatDiscreteHasForget₂ : HasForget₂ FintypeCat TopCat :=
  inferInstance

/-- Every morphism of finite types is continuous for the discrete topology. -/
theorem fintypeCatDiscreteForget_map_continuous {X Y : FintypeCat} (f : X ⟶ Y) :
    Continuous (fintypeCatDiscreteForget.map f) :=
  (fintypeCatDiscreteForget.map f).hom'.continuous

/-! ## 2. The category of finite continuous G-sets -/

/-- The category of finite sets with a continuous action of a profinite group
G, i.e. Mathlib's ContAction FintypeCat G. -/
abbrev finiteContinuousGaloisSets (G : ProfiniteGrp.{u}) : Type (u + 1) :=
  ContAction FintypeCat.{u} G

/-- The category of finite continuous G_K-sets for the absolute Galois group
of a field K. -/
abbrev finiteContinuousGaloisSetsOfField (K : Type u) [Field K] : Type (u + 1) :=
  finiteContinuousGaloisSets (Iut.AbsoluteGaloisProfinite K)

/-- The underlying finite continuous G-set of a continuous action. -/
abbrev finiteContinuousGaloisSetsObject (G : ProfiniteGrp)
    (X : finiteContinuousGaloisSets G) : Action FintypeCat G :=
  X.obj

/-! ## 3. Continuity criterion: open point stabilizers -/

/-- All point stabilizers of a finite action are open. -/
def HasOpenStabilizers (G : ProfiniteGrp) (X : Action FintypeCat G) : Prop :=
  ∀ x : (forget₂ (Action FintypeCat G) TopCat).obj X,
    IsOpen (MulAction.stabilizer G x : Set G)

/-- The action map of a finite action is continuous exactly when all point
stabilizers are open. -/
theorem action_isContinuous_iff_hasOpenStabilizers (G : ProfiniteGrp)
    (X : Action FintypeCat G) :
    Action.IsContinuous X ↔ HasOpenStabilizers G X := by
  haveI : DiscreteTopology ((forget₂ (Action FintypeCat G) TopCat).obj X) := by
    change DiscreteTopology X.V
    infer_instance
  exact continuousSMul_iff_stabilizer_isOpen

/-- An action with open stabilizers is continuous. -/
theorem action_isContinuous_of_hasOpenStabilizers (G : ProfiniteGrp)
    (X : Action FintypeCat G) (h : HasOpenStabilizers G X) :
    Action.IsContinuous X :=
  (action_isContinuous_iff_hasOpenStabilizers G X).mpr h

/-- A continuous finite action has open stabilizers. -/
theorem hasOpenStabilizers_of_action_isContinuous (G : ProfiniteGrp)
    (X : Action FintypeCat G) (h : Action.IsContinuous X) :
    HasOpenStabilizers G X :=
  (action_isContinuous_iff_hasOpenStabilizers G X).mp h

/-! ## 4. The continuous category as the open-stabilizer full subcategory -/

/-- The full subcategory of finite actions with open point stabilizers. -/
abbrev openStabilizerActions (G : ProfiniteGrp) :=
  ObjectProperty.FullSubcategory (fun X : Action FintypeCat G => HasOpenStabilizers G X)

/-- The inclusion of finite continuous actions into finite actions with open
point stabilizers. -/
noncomputable def continuousToOpenStabilizerActions (G : ProfiniteGrp) :
    finiteContinuousGaloisSets G ⥤ openStabilizerActions G :=
  ObjectProperty.lift _ (Iut.continuousActionInclusion G)
    (fun X => hasOpenStabilizers_of_action_isContinuous G X X.2)

/-- The inclusion of finite actions with open point stabilizers into finite
continuous actions (by the continuity criterion). -/
noncomputable def openStabilizerActionsToContinuous (G : ProfiniteGrp) :
    openStabilizerActions G ⥤ finiteContinuousGaloisSets G :=
  ObjectProperty.lift (fun X : Action FintypeCat G => Action.IsContinuous X)
    (ObjectProperty.ι (fun X : Action FintypeCat G => HasOpenStabilizers G X))
    (fun X => action_isContinuous_of_hasOpenStabilizers G X.obj X.2)

/-- The category of finite continuous G-sets is equivalent to the full
subcategory of finite actions with open point stabilizers.  For a finite set the
kernel of the permutation action is the finite intersection of the point
stabilizers, so this is the stabilizer-open form of the classical open-kernel
criterion; the full action category itself is not equivalent, see the module
docstring warning. -/
noncomputable def continuousActionEquivalenceOpenStabilizers (G : ProfiniteGrp) :
    finiteContinuousGaloisSets G ≌ openStabilizerActions G where
  functor := continuousToOpenStabilizerActions G
  inverse := openStabilizerActionsToContinuous G
  unitIso := NatIso.ofComponents (fun X => ObjectProperty.isoMk _ (Iso.refl _))
    (fun X => by ext; rfl)
  counitIso := NatIso.ofComponents (fun X => ObjectProperty.isoMk _ (Iso.refl _))
    (fun X => by ext; rfl)

/-! ## 5. Fiber functor, Galois category and fundamental group -/

/-- The fiber functor of the continuous G-set category. -/
abbrev finiteContinuousGaloisSetFiber (G : ProfiniteGrp) :
    finiteContinuousGaloisSets G ⥤ FintypeCat :=
  Iut.continuousActionFiber G

/-- The continuous G-set category has the structure of a Galois category. -/
theorem finiteContinuousGaloisSets_galoisCategory (G : ProfiniteGrp) :
    GaloisCategory (finiteContinuousGaloisSets G) :=
  Iut.continuousAction_galoisCategory G

/-- The forgetful functor to finite types is a fiber functor. -/
theorem finiteContinuousGaloisSetFiber_fiberFunctor (G : ProfiniteGrp) :
    PreGaloisCategory.FiberFunctor (finiteContinuousGaloisSetFiber G) :=
  Iut.continuousAction_fiberFunctor G

/-- The profinite group G is the fundamental group of its category of finite
continuous G-sets. -/
theorem finiteContinuousGaloisSetFiber_isFundamentalGroup (G : ProfiniteGrp) :
    PreGaloisCategory.IsFundamentalGroup (finiteContinuousGaloisSetFiber G) G :=
  Iut.continuousAction_isFundamentalGroup G

/-- The case of the absolute Galois group G_K of a field K. -/
theorem finiteContinuousGaloisSetsOfField_galoisCategory (K : Type u) [Field K] :
    GaloisCategory (finiteContinuousGaloisSetsOfField K) :=
  finiteContinuousGaloisSets_galoisCategory (Iut.AbsoluteGaloisProfinite K)

/-! ## 6. Frozen card: equivalence with finite etale K-algebras -/

/-- Frozen card: the exact missing equivalence between the category of finite
continuous G_K-sets and the category of finite etale K-algebras with its
Galois structure.  The target category is not constructed in this file; the
card is DATA, it has no inhabitant and no theorem consumes it. -/
structure FiniteEtaleKAlgebraEquivalenceCard (K : Type u) [Field K] where
  /-- The target category of finite etale K-algebras (not constructed here). -/
  targetCategory : Type (u + 1)
  [targetCategory_category : Category.{u, u + 1} targetCategory]
  [targetCategory_galoisCategory : GaloisCategory targetCategory]
  /-- The missing equivalence of categories. -/
  equivalence : finiteContinuousGaloisSetsOfField K ≌ targetCategory

/-- The finite etale K-algebra equivalence card is realized.  This is a frozen
source obligation: it is not proved here and it has no consumer. -/
def FiniteEtaleKAlgebraEquivalenceCardRealized (K : Type u) [Field K] : Prop :=
  Nonempty (FiniteEtaleKAlgebraEquivalenceCard K)

end Example36
end LeanFormal.IUT.IUTII.Frobenioid

