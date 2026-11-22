/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal IUT/ABC contributors
-/
import LeanFormal.IUT.IUTII.Frobenioid.Example36TateModuleProfinite
import LeanFormal.IUT.IUTII.Frobenioid.Example36TorsionAllLevels
import LeanFormal.IUT.IUTII.Frobenioid.Example36ProfiniteLimitTopology
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The actual G_K action on the pro-2 Tate module of y^2 = x^3 - x

Foundation F4/Galois.  This module puts an actual action of the absolute Galois
group G_K = Gal(K/Q) of the separable closure K of Q on the finite 2-power
torsion levels E[2^(n+1)] of the concrete curve y^2 = x^3 - x, proves that the
level actions commute with the transition maps [2], lifts them to the actual
general pro-2 inverse limit constructed in Example36TorsionAllLevels, and
packages the resulting pro-2 Tate module with its G_K action and compatible
projections.

## Content

* tateGaloisGroup: the actual absolute Galois group, as the group of
  Q-algebra automorphisms of the separable closure K of Q.
* tatePowerTwoLevelGaloisAction n sigma: the actual additive automorphism of
  E[2^(n+1)] induced by sigma (ABCBridge Galois galoisTorsionEquiv, i.e.
  Mathlib's Point.map of sigma.toAlgHom restricted to torsion).
* tatePowerTwoLevelGaloisActionHom: the monoid hom G_K -> (E[2^(n+1)] ~= E[2^(n+1)])
  with the identity and composition laws.
* tatePowerTwoLevelGaloisAction_transition: the level actions commute with the
  transition maps [2]: applying [2] after the action equals the action after [2].
* tatePowerTwoProfiniteLevelGaloisAction: the same automorphism as a morphism of
  finite discrete profinite groups; the successor compatibility above gives a
  natural endomorphism of the N^op diagram
  (tatePowerTwoProfiniteDiagramGaloisAction via NatTrans.ofOpSequence).
* tatePowerTwoProfiniteLimitGaloisCone / ...LimitGaloisAction: the action on the
  actual pro-2 limit, defined by the universal property of the limit cone, with
  projection compatibility (fac) and the identity/composition laws proved by
  uniqueness (IsLimit.uniq).  The result is an actual automorphism
  (tatePowerTwoProfiniteLimitGaloisIso).
* actualProTwoTateGaloisModule: the packaged pro-2 Tate module with its G_K
  action; it agrees field by field with the actual pro-2 realization
  tateTwoProLTateModuleProjSystemData of Example36TateModuleProfinite.
* tateProfiniteLimitInducedEndomorphism and its projection and composition
  lemmas: the functoriality of the limit action, proved via IsLimit.hom_ext with
  an explicitly typed projection.
* tateProfiniteLimitGaloisAction_mul and tateProfiniteLimitGaloisIso: the
  composition law of the actual limit action and the resulting automorphism of
  the pro-2 Tate module.
* tatePowerTwoLevelMulAction_stabilizer_isOpen: Krull-type continuity at the
  finite levels: for every finite level point the stabilizer in the Krull
  topology of G_K is open (in the affine case the intersection of the open
  stabilizers of the two algebraic coordinates).
* tatePowerTwoLevelMulAction_continuousSMul and
  tatePowerTwoLevelGaloisAction_continuous: the actual continuity of the
  finite-level action maps G_K x E[2^(n+1)] -> E[2^(n+1)] for the Krull
  topology and the discrete topology.
* tatePowerTwoProfiniteLevelGaloisAction_continuous: continuity of the finite
  profinite-level actions.
* tateProfiniteLimitProjection_continuous, tateProfiniteLimitProjectionFamily
  and its injectivity/closed-embedding theorems: the pro-2 Tate module is a
  closed subspace of the product of its finite levels via the family of limit
  projections.
* tateProfiniteLimitGaloisAction_continuous: the ACTUAL joint continuity of the
  map G_K x T_2 -> T_2, derived from the finite-level continuity and the closed
  embedding of T_2 into the product of its finite levels.
* tatePowerTwoLevelGaloisLinearEquiv / tatePowerTwoLevelGaloisGeneralLinear:
  the level action is `ZMod (2^(n+1))`-linear, giving the basis-free
  general-linear representation `G_K -> GL(E[2^(n+1)])`.
* tatePowerTwoLevelGaloisMatrix: the matrix of the level action relative to a
  rank-two basis, with identity and composition laws
  (`..._one`, `..._mul`) and invertibility (`..._isUnit`).
* tateLevelTwo_cases, tateLevelTwoPointMinusOneZero_eq_add,
  tateLevelTwoCoordinateMap(_injective/_surjective),
  tateLevelTwoCoordinateEquiv, tateLevelTwoBasis: an unconditional rank-two
  `ZMod 2`-basis of `E[2]` built from the actual points `(0,0)`, `(1,0)`,
  `(-1,0)`; consequently tateLevelTwoGaloisMatrix is an actual `2 x 2` matrix
  representation over `ZMod 2` (`_one`, `_mul`, `_isUnit`).
* fullTateAndSourceIdentificationCard: the only frozen card.  It is the
  existing full arithmetic Tate module card (SourceFullTateModuleData) together
  with the existing source curve pi card; it is NOT claimed or constructed in
  this file and no pro-2 statement is identified with the source anabelioid.

## Actual joint continuity of the limit action

The actual action on the limit is constructed, with projection compatibility,
identity law, composition law and automorphism isomorphisms.  The finite-level
action maps are continuous for the Krull topology (open stabilizers,
ContinuousSMul, and continuity of the map G_K x E[2^(n+1)] -> E[2^(n+1)]).

The joint continuity of the map G_K x T_2 -> T_2 is PROVED in this file.  The
auxiliary file Example36ProfiniteLimitTopology proves the initial-topology
universal property of the bundled ProfiniteGrp limit (a map into the limit is
continuous iff all composites with the limit projections are continuous) and a
closed-embedding description of the projection map.  In this file the family of
all limit projections
tateProfiniteLimitProjectionFamily : T_2 -> prod_n E[2^(n+1)]
is shown to be continuous, injective and (since T_2 is compact and the product
is Hausdorff) a closed embedding; composing it with the limit action gives the
map p |-> (n |-> proj_n (action p.1 p.2)), whose continuity follows pointwise
from the finite-level continuity.  The closed embedding then yields continuity
of the action itself (Topology.IsEmbedding.continuous_iff), and the packaged
structure ProTwoTateGaloisModule records the continuity field
limitAction_continuous.  No card is used for the pro-2 action or its
continuity.

## Boundary

The pro-2 limit is the general small-diagram limit of the finite levels; its
Galois action is defined purely by the universal property and the finite-level
actions, so it is actual (not a fake action).  The finite-level Krull
continuity (open stabilizers) and the joint continuity of the limit action
G_K x T_2 -> T_2 are both proved.  The full arithmetic Tate module
prod_l T_l(E) and the source curve pi1 identification remain frozen in the
existing cards.  No theta/q-pilot or Anabelian claim is made.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36
namespace TateGaloisAction

open CategoryTheory WeierstrassCurve
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36

local instance instDecidableEqTateGeometricBase : DecidableEq tateGeometricBase :=
  Classical.decEq tateGeometricBase

/-- The actual absolute Galois group acting: the group of Q-algebra
automorphisms of the separable closure of Q (underlying the profinite group
Iut.AbsoluteGaloisProfinite Q). -/
abbrev tateGaloisGroup : Type := Gal(tateGeometricBase/ℚ)

/-! ## The action on each finite level E[2^(n+1)] -/

/-- The actual action of the absolute Galois group on the finite level
E[2^(n+1)]: the automorphism of the torsion subgroup induced by the field
automorphism (Mathlib Point.map of sigma.toAlgHom, restricted to torsion). -/
noncomputable def tatePowerTwoLevelGaloisAction (n : ℕ) (σ : tateGaloisGroup) :
    tatePowerTwoLevel n ≃+ tatePowerTwoLevel n :=
  LeanFormal.IUT.ABCBridge.Galois.galoisTorsionEquiv (k := ℚ) (K := tateGeometricBase)
    curveY2EqX3SubX (2 ^ n) σ

/-- The underlying effect of the level action is Mathlib's Point.map. -/
theorem tatePowerTwoLevelGaloisAction_apply (n : ℕ) (σ : tateGaloisGroup)
    (P : tatePowerTwoLevel n) :
    ((tatePowerTwoLevelGaloisAction n σ P : tatePowerTwoLevel n) :
        tateAllLevelsPointType) =
      WeierstrassCurve.Affine.Point.map (σ : tateGeometricBase →ₐ[ℚ] tateGeometricBase)
        (P : tateAllLevelsPointType) :=
  LeanFormal.IUT.ABCBridge.Galois.galoisTorsionEquiv_coe
    (k := ℚ) (K := tateGeometricBase) curveY2EqX3SubX (2 ^ n) σ P

/-- The identity acts trivially on a finite level. -/
theorem tatePowerTwoLevelGaloisAction_one_apply (n : ℕ) (P : tatePowerTwoLevel n) :
    tatePowerTwoLevelGaloisAction n 1 P = P :=
  LeanFormal.IUT.ABCBridge.Galois.galoisTorsionEquiv_one_apply
    (k := ℚ) (K := tateGeometricBase) curveY2EqX3SubX (2 ^ n) P

/-- The level action is a group action: action (sigma * tau) = action sigma after
action tau. -/
theorem tatePowerTwoLevelGaloisAction_mul_apply (n : ℕ) (σ τ : tateGaloisGroup)
    (P : tatePowerTwoLevel n) :
    tatePowerTwoLevelGaloisAction n (σ * τ) P =
      tatePowerTwoLevelGaloisAction n σ (tatePowerTwoLevelGaloisAction n τ P) :=
  LeanFormal.IUT.ABCBridge.Galois.galoisTorsionEquiv_mul_apply
    (k := ℚ) (K := tateGeometricBase) curveY2EqX3SubX (2 ^ n) σ τ P

/-- **Compatibility with the transition maps.**  Applying [2] after the level
action equals applying the level action after [2]. -/
theorem tatePowerTwoLevelGaloisAction_transition (n : ℕ) (σ : tateGaloisGroup)
    (P : tatePowerTwoLevel (n + 1)) :
    tatePowerTwoTransition n (tatePowerTwoLevelGaloisAction (n + 1) σ P) =
      tatePowerTwoLevelGaloisAction n σ (tatePowerTwoTransition n P) := by
  apply Subtype.ext
  change (2 : ℕ) • ((tatePowerTwoLevelGaloisAction (n + 1) σ P) : tateAllLevelsPointType) =
    ((tatePowerTwoLevelGaloisAction n σ (tatePowerTwoTransition n P)) :
      tateAllLevelsPointType)
  rw [tatePowerTwoLevelGaloisAction_apply, tatePowerTwoLevelGaloisAction_apply]
  change (2 : ℕ) •
      (WeierstrassCurve.Affine.Point.map
        (σ : tateGeometricBase →ₐ[ℚ] tateGeometricBase)
        (P : tateAllLevelsPointType)) =
    (WeierstrassCurve.Affine.Point.map
        (σ : tateGeometricBase →ₐ[ℚ] tateGeometricBase))
      ((2 : ℕ) • (P : tateAllLevelsPointType))
  rw [AddMonoidHom.map_nsmul]

/-! ## The induced endomorphism of the N^op diagram and of the actual limit -/

/-- The same automorphism at the finite discrete profinite group of the level. -/
noncomputable def tatePowerTwoProfiniteLevelGaloisAction (n : ℕ) (σ : tateGaloisGroup) :
    tatePowerTwoProfiniteTateLevel n ⟶ tatePowerTwoProfiniteTateLevel n :=
  ProfiniteGrp.ofFiniteGrpHom
    (FiniteGrp.ofHom
      ((AddEquiv.toMultiplicative (tatePowerTwoLevelGaloisAction (n + 1) σ)).toMonoidHom))

/-- The underlying additive effect of the profinite level action. -/
theorem tatePowerTwoProfiniteLevelGaloisAction_apply (n : ℕ) (σ : tateGaloisGroup)
    (u : tatePowerTwoProfiniteTateLevel n) :
    (tatePowerTwoProfiniteLevelGaloisAction n σ u :
        tatePowerTwoProfiniteTateLevel n) =
      Multiplicative.ofAdd
        (tatePowerTwoLevelGaloisAction (n + 1) σ (Multiplicative.toAdd u)) :=
  rfl

/-- **Successor compatibility** for the profinite level actions: the level
actions are natural with respect to the transitions [2]. -/
theorem tatePowerTwoProfiniteLevelGaloisAction_transition (n : ℕ) (σ : tateGaloisGroup) :
    tatePowerTwoProfiniteTransition n ≫ tatePowerTwoProfiniteLevelGaloisAction n σ =
      tatePowerTwoProfiniteLevelGaloisAction (n + 1) σ ≫ tatePowerTwoProfiniteTransition n := by
  apply ProfiniteGrp.hom_ext
  apply ContinuousMonoidHom.ext
  intro u
  apply Multiplicative.ext
  simp only [ProfiniteGrp.coe_comp, Function.comp_apply,
    tatePowerTwoProfiniteLevelGaloisAction_apply]
  exact congrArg Multiplicative.ofAdd
    (tatePowerTwoLevelGaloisAction_transition (n + 1) σ
      (Multiplicative.toAdd u)).symm

/-- The actual N^op diagram of finite 2-power torsion levels, in reducible form. -/
noncomputable abbrev tateProfiniteDiagram : ℕᵒᵖ ⥤ ProfiniteGrp :=
  Functor.ofOpSequence tatePowerTwoProfiniteTransition

/-- The actual pro-2 inverse limit, in reducible form. -/
noncomputable abbrev tateProfiniteLimit : ProfiniteGrp :=
  (ProfiniteGrp.limitCone tateProfiniteDiagram).pt

/-- The actual projections from the limit, in reducible form. -/
noncomputable abbrev tateProfiniteLimitProjection (n : ℕ) :
    tateProfiniteLimit ⟶ tatePowerTwoProfiniteTateLevel n :=
  (ProfiniteGrp.limitCone tateProfiniteDiagram).π.app (Opposite.op n)

/-- The level actions give a natural endomorphism of the actual N^op diagram of
finite 2-power torsion levels.  The diagram is the same functor as
tateProfiniteDiagram (definitionally), written in unfolded form so that
the components have their concrete types. -/
noncomputable def tateProfiniteDiagramGaloisAction (σ : tateGaloisGroup) :
    Functor.ofOpSequence tatePowerTwoProfiniteTransition ⟶
      Functor.ofOpSequence tatePowerTwoProfiniteTransition :=
  NatTrans.ofOpSequence (fun n => tatePowerTwoProfiniteLevelGaloisAction n σ) (by
    intro n
    simp only [Functor.ofOpSequence_map_homOfLE_succ]
    exact tatePowerTwoProfiniteLevelGaloisAction_transition n σ)

/-- The components of the diagram action are the finite-level actions. -/
@[simp]
theorem tateProfiniteDiagramGaloisAction_app (σ : tateGaloisGroup) (n : ℕ) :
    (tateProfiniteDiagramGaloisAction σ).app (Opposite.op n) =
      tatePowerTwoProfiniteLevelGaloisAction n σ :=
  rfl

/-- The actual action of the absolute Galois group on the pro-2 Tate module,
obtained by postcomposing the actual limit cone with the diagram action and
lifting through the universal property of the limit. -/
noncomputable def tateProfiniteLimitGaloisAction (σ : tateGaloisGroup) :
    tateProfiniteLimit ⟶ tateProfiniteLimit :=
  (ProfiniteGrp.limitConeIsLimit tateProfiniteDiagram).lift
    ((Limits.Cone.postcompose (tateProfiniteDiagramGaloisAction σ)).obj
      (ProfiniteGrp.limitCone tateProfiniteDiagram))

/-- **Projection compatibility** of the limit action: the action commutes with
the projections to the finite levels. -/
theorem tateProfiniteLimitGaloisAction_projection (n : ℕ) (σ : tateGaloisGroup) :
    tateProfiniteLimitGaloisAction σ ≫ tateProfiniteLimitProjection n =
      tateProfiniteLimitProjection n ≫ tatePowerTwoProfiniteLevelGaloisAction n σ := by
  have h := (ProfiniteGrp.limitConeIsLimit tateProfiniteDiagram).fac
    ((Limits.Cone.postcompose (tateProfiniteDiagramGaloisAction σ)).obj
      (ProfiniteGrp.limitCone tateProfiniteDiagram)) ⟨n⟩
  simp only [Limits.Cone.postcompose_obj_π, NatTrans.comp_app] at h
  exact h
/-! ## The level action is a group action, and its limit is an automorphism -/

/-- The identity acts trivially at the profinite finite level. -/
theorem tatePowerTwoProfiniteLevelGaloisAction_one (n : ℕ) :
    tatePowerTwoProfiniteLevelGaloisAction n 1 = 𝟙 (tatePowerTwoProfiniteTateLevel n) := by
  apply ProfiniteGrp.hom_ext
  apply ContinuousMonoidHom.ext
  intro u
  apply Multiplicative.ext
  simp only [tatePowerTwoProfiniteLevelGaloisAction_apply,
    tatePowerTwoLevelGaloisAction_one_apply]
  simp

/-- Composition law at the profinite finite level. -/
theorem tatePowerTwoProfiniteLevelGaloisAction_mul (n : ℕ) (σ τ : tateGaloisGroup) :
    tatePowerTwoProfiniteLevelGaloisAction n (σ * τ) =
      tatePowerTwoProfiniteLevelGaloisAction n τ ≫
        tatePowerTwoProfiniteLevelGaloisAction n σ := by
  apply ProfiniteGrp.hom_ext
  apply ContinuousMonoidHom.ext
  intro u
  apply Multiplicative.ext
  simp only [ProfiniteGrp.coe_comp, Function.comp_apply,
    tatePowerTwoProfiniteLevelGaloisAction_apply,
    tatePowerTwoLevelGaloisAction_mul_apply]
  simp

/-- The identity acts trivially on the actual pro-2 Tate module. -/
theorem tateProfiniteLimitGaloisAction_one :
    tateProfiniteLimitGaloisAction 1 = 𝟙 tateProfiniteLimit := by
  have h_id : (𝟙 tateProfiniteLimit) =
      (ProfiniteGrp.limitConeIsLimit tateProfiniteDiagram).lift
        (ProfiniteGrp.limitCone tateProfiniteDiagram) :=
    (ProfiniteGrp.limitConeIsLimit tateProfiniteDiagram).uniq
      (ProfiniteGrp.limitCone tateProfiniteDiagram)
      (𝟙 tateProfiniteLimit) (fun j => by erw [Category.id_comp])
  have h_act : tateProfiniteLimitGaloisAction 1 =
      (ProfiniteGrp.limitConeIsLimit tateProfiniteDiagram).lift
        (ProfiniteGrp.limitCone tateProfiniteDiagram) := by
    refine (ProfiniteGrp.limitConeIsLimit tateProfiniteDiagram).uniq
      (ProfiniteGrp.limitCone tateProfiniteDiagram)
      (tateProfiniteLimitGaloisAction 1) (fun j => ?_)
    erw [tateProfiniteLimitGaloisAction_projection,
      tatePowerTwoProfiniteLevelGaloisAction_one, Category.comp_id]
  rw [h_act, ← h_id]

/-- The endomorphism of the actual limit induced by a natural endomorphism of
the N^op diagram, through the universal property of the limit cone. -/
noncomputable def tateProfiniteLimitInducedEndomorphism
    (α : tateProfiniteDiagram ⟶ tateProfiniteDiagram) :
    tateProfiniteLimit ⟶ tateProfiniteLimit :=
  (ProfiniteGrp.limitConeIsLimit tateProfiniteDiagram).lift
    ((Limits.Cone.postcompose α).obj (ProfiniteGrp.limitCone tateProfiniteDiagram))

/-- The projections identify the induced limit endomorphism with the components
of the natural endomorphism. -/
theorem tateProfiniteLimitInducedEndomorphism_projection
    (α : tateProfiniteDiagram ⟶ tateProfiniteDiagram) (j : ℕᵒᵖ) :
    tateProfiniteLimitInducedEndomorphism α ≫
        (ProfiniteGrp.limitCone tateProfiniteDiagram).π.app j =
      (ProfiniteGrp.limitCone tateProfiniteDiagram).π.app j ≫ α.app j :=
  (ProfiniteGrp.limitConeIsLimit tateProfiniteDiagram).fac
    ((Limits.Cone.postcompose α).obj (ProfiniteGrp.limitCone tateProfiniteDiagram)) j

/-- Functoriality of the induced limit endomorphism: composition of diagram
endomorphisms maps to composition of limit endomorphisms. -/
theorem tateProfiniteLimitInducedEndomorphism_comp
    (α β : tateProfiniteDiagram ⟶ tateProfiniteDiagram) :
    tateProfiniteLimitInducedEndomorphism (α ≫ β) =
      tateProfiniteLimitInducedEndomorphism α ≫
        tateProfiniteLimitInducedEndomorphism β := by
  apply (ProfiniteGrp.limitConeIsLimit tateProfiniteDiagram).hom_ext
  intro j
  let projection : tateProfiniteLimit ⟶ tateProfiniteDiagram.obj j :=
    (ProfiniteGrp.limitCone tateProfiniteDiagram).π.app j
  have hprojection (γ : tateProfiniteDiagram ⟶ tateProfiniteDiagram) :
      tateProfiniteLimitInducedEndomorphism γ ≫ projection =
        projection ≫ γ.app j :=
    tateProfiniteLimitInducedEndomorphism_projection γ j
  change tateProfiniteLimitInducedEndomorphism (α ≫ β) ≫ projection =
    (tateProfiniteLimitInducedEndomorphism α ≫
      tateProfiniteLimitInducedEndomorphism β) ≫ projection
  rw [hprojection, Category.assoc, hprojection, ← Category.assoc, hprojection]
  exact (Category.assoc projection (α.app j) (β.app j)).symm

/-- The actual limit action is the induced limit endomorphism of the diagram
action. -/
theorem tateProfiniteLimitGaloisAction_eq_induced (σ : tateGaloisGroup) :
    tateProfiniteLimitGaloisAction σ =
      tateProfiniteLimitInducedEndomorphism
        (tateProfiniteDiagramGaloisAction σ) :=
  rfl

/-- Composition law for the actual action on the pro-2 Tate module: the diagram
actions compose, and the induced limit endomorphism is functorial. -/
theorem tateProfiniteLimitGaloisAction_mul (σ τ : tateGaloisGroup) :
    tateProfiniteLimitGaloisAction (σ * τ) =
      tateProfiniteLimitGaloisAction τ ≫
        tateProfiniteLimitGaloisAction σ := by
  have h : tateProfiniteDiagramGaloisAction (σ * τ) =
      tateProfiniteDiagramGaloisAction τ ≫
        tateProfiniteDiagramGaloisAction σ := by
    apply NatTrans.ext
    funext j
    cases j with
    | op n =>
      exact tatePowerTwoProfiniteLevelGaloisAction_mul n σ τ
  rw [tateProfiniteLimitGaloisAction_eq_induced,
    tateProfiniteLimitGaloisAction_eq_induced,
    tateProfiniteLimitGaloisAction_eq_induced, h,
    tateProfiniteLimitInducedEndomorphism_comp]

/-- The action of an absolute Galois element on the actual pro-2 Tate module is
an automorphism (with inverse the action of the inverse element). -/
noncomputable def tateProfiniteLimitGaloisIso (σ : tateGaloisGroup) :
    tateProfiniteLimit ≅ tateProfiniteLimit where
  hom := tateProfiniteLimitGaloisAction σ
  inv := tateProfiniteLimitGaloisAction σ⁻¹
  hom_inv_id := by
    rw [← tateProfiniteLimitGaloisAction_mul, inv_mul_cancel,
      tateProfiniteLimitGaloisAction_one]
  inv_hom_id := by
    rw [← tateProfiniteLimitGaloisAction_mul, mul_inv_cancel,
      tateProfiniteLimitGaloisAction_one]

/-! ## Krull continuity of the finite-level action (open stabilizers) -/

section FiniteLevelContinuity

/-- The separable closure is algebraic and integral over Q (the latter obtained
from the relative separable closure instance; typeclass synthesis needs the
explicit term). -/
local instance : Algebra.IsAlgebraic ℚ tateGeometricBase :=
  separableClosure.isAlgebraic ℚ (AlgebraicClosure ℚ)

local instance : Algebra.IsIntegral ℚ tateGeometricBase :=
  Algebra.IsAlgebraic.isIntegral

/-- The discrete topology on a finite torsion level. -/
local instance tatePowerTwoLevelTopology (n : ℕ) : TopologicalSpace (tatePowerTwoLevel n) := ⊥

local instance tatePowerTwoLevelDiscrete (n : ℕ) : DiscreteTopology (tatePowerTwoLevel n) :=
  ⟨rfl⟩

local instance tatePowerTwoLevelMultiplicativeDiscrete (n : ℕ) :
    DiscreteTopology (Multiplicative (tatePowerTwoLevel n)) :=
  ⟨rfl⟩

/-- The action of the absolute Galois group on the multiplicative copy of the
finite level E[2^(n+1)]. -/
noncomputable local instance tatePowerTwoLevelMulAction (n : ℕ) :
    MulAction tateGaloisGroup (Multiplicative (tatePowerTwoLevel n)) where
  smul σ u :=
    Multiplicative.ofAdd
      (tatePowerTwoLevelGaloisAction n σ (Multiplicative.toAdd u))
  one_smul u := by
    apply Multiplicative.ext
    exact tatePowerTwoLevelGaloisAction_one_apply n (Multiplicative.toAdd u)
  mul_smul σ τ u := by
    apply Multiplicative.ext
    exact tatePowerTwoLevelGaloisAction_mul_apply n σ τ (Multiplicative.toAdd u)

/-- **Krull-type continuity at the finite levels.**  For every point of the
finite level E[2^(n+1)] the stabilizer in the Krull topology of the absolute
Galois group is open: it is the stabilizer of the underlying point, hence (in
the affine case) the intersection of the open stabilizers of its two algebraic
coordinates. -/
theorem tatePowerTwoLevelMulAction_stabilizer_isOpen (n : ℕ)
    (u : Multiplicative (tatePowerTwoLevel n)) :
    IsOpen (MulAction.stabilizer tateGaloisGroup u : Set tateGaloisGroup) := by
  classical
  set P : tatePowerTwoLevel n := Multiplicative.toAdd u with hP
  have hset : (MulAction.stabilizer tateGaloisGroup u : Set tateGaloisGroup) =
      {σ : tateGaloisGroup | tatePowerTwoLevelGaloisAction n σ P = P} := by
    ext σ
    constructor
    · intro h
      have h' : σ • u = u := by
        simpa using h
      exact congrArg Multiplicative.toAdd h'
    · intro h
      have h' : σ • u = u := Multiplicative.ext h
      simpa using h'
  rw [hset]
  cases hpt : (P : tateAllLevelsPointType) with
  | zero =>
    have h0 : {σ : tateGaloisGroup |
        tatePowerTwoLevelGaloisAction n σ P = P} = Set.univ := by
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      apply Subtype.ext
      rw [tatePowerTwoLevelGaloisAction_apply, hpt]
      exact WeierstrassCurve.Affine.Point.map_zero
        (f := (σ : tateGeometricBase →ₐ[ℚ] tateGeometricBase))
    rw [h0]
    exact isOpen_univ
  | some x y hns =>
    have h2 : {σ : tateGaloisGroup | tatePowerTwoLevelGaloisAction n σ P = P} =
        (MulAction.stabilizer tateGaloisGroup x : Set tateGaloisGroup) ∩
          (MulAction.stabilizer tateGaloisGroup y : Set tateGaloisGroup) := by
      ext σ
      constructor
      · intro h
        have hcoord := congrArg
          (fun Q : tatePowerTwoLevel n => (Q : tateAllLevelsPointType)) h
        rw [tatePowerTwoLevelGaloisAction_apply, hpt,
          WeierstrassCurve.Affine.Point.map_some] at hcoord
        have hpair := (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp hcoord
        constructor
        · exact MulAction.mem_stabilizer_iff.mpr (by simpa using hpair.1)
        · exact MulAction.mem_stabilizer_iff.mpr (by simpa using hpair.2)
      · intro h
        apply Subtype.ext
        rw [tatePowerTwoLevelGaloisAction_apply, hpt,
          WeierstrassCurve.Affine.Point.map_some]
        have hx : σ • x = x := by simpa using h.1
        have hy : σ • y = y := by simpa using h.2
        exact (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr
          ⟨by simpa using hx, by simpa using hy⟩
    rw [h2]
    exact (stabilizer_isOpen_of_isIntegral x).inter
      (stabilizer_isOpen_of_isIntegral y)

/-- The finite-level action is continuous for the Krull topology on the Galois
group and the discrete topology on the finite level (ContinuousSMul form). -/
theorem tatePowerTwoLevelMulAction_continuousSMul (n : ℕ) :
    ContinuousSMul tateGaloisGroup (Multiplicative (tatePowerTwoLevel n)) := by
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro u
  exact tatePowerTwoLevelMulAction_stabilizer_isOpen n u

/-- **Actual continuity of the finite-level action**: the map
G_K x E[2^(n+1)] -> E[2^(n+1)] is continuous for the Krull topology on G_K and
the discrete topology on the finite level. -/
theorem tatePowerTwoLevelGaloisAction_continuous (n : ℕ) :
    Continuous (fun p : tateGaloisGroup × tatePowerTwoLevel n =>
      tatePowerTwoLevelGaloisAction n p.1 p.2) := by
  have hsmul : Continuous
      (fun p : tateGaloisGroup × Multiplicative (tatePowerTwoLevel n) =>
        p.1 • p.2) :=
    (tatePowerTwoLevelMulAction_continuousSMul n).continuous_smul
  have hcomp : Continuous
      (fun p : tateGaloisGroup × tatePowerTwoLevel n =>
        (p.1 • Multiplicative.ofAdd p.2)) :=
    hsmul.comp (continuous_fst.prodMk
      (continuous_ofAdd.comp continuous_snd))
  have hfinal : Continuous
      (fun p : tateGaloisGroup × tatePowerTwoLevel n =>
        Multiplicative.toAdd (p.1 • Multiplicative.ofAdd p.2)) :=
    continuous_toAdd.comp hcomp
  have hfun : (fun p : tateGaloisGroup × tatePowerTwoLevel n =>
        Multiplicative.toAdd (p.1 • Multiplicative.ofAdd p.2)) =
      (fun p : tateGaloisGroup × tatePowerTwoLevel n =>
        tatePowerTwoLevelGaloisAction n p.1 p.2) := by
    funext p
    change Multiplicative.toAdd
        (Multiplicative.ofAdd (tatePowerTwoLevelGaloisAction n p.1
          (Multiplicative.toAdd (Multiplicative.ofAdd p.2)))) =
      tatePowerTwoLevelGaloisAction n p.1 p.2
    rw [toAdd_ofAdd, toAdd_ofAdd]
  rw [hfun] at hfinal
  exact hfinal

end FiniteLevelContinuity

/-! ## Joint continuity of the limit action -/

section LimitJointContinuity

local instance tatePowerTwoLevelTopologyJoint (n : ℕ) :
    TopologicalSpace (tatePowerTwoLevel n) := ⊥

local instance tatePowerTwoLevelDiscreteJoint (n : ℕ) :
    DiscreteTopology (tatePowerTwoLevel n) := ⟨rfl⟩

local instance tatePowerTwoLevelMultiplicativeDiscreteJoint (n : ℕ) :
    DiscreteTopology (Multiplicative (tatePowerTwoLevel n)) := ⟨rfl⟩

/-- Continuity of the finite profinite-level action maps, obtained from the
additive finite-level continuity and the definition of the level actions. -/
theorem tatePowerTwoProfiniteLevelGaloisAction_continuous (n : ℕ) :
    Continuous
      (fun p : tateGaloisGroup × tatePowerTwoProfiniteTateLevel n =>
        tatePowerTwoProfiniteLevelGaloisAction n p.1 p.2) := by
  have h := (tatePowerTwoLevelGaloisAction_continuous (n + 1)).comp
    (continuous_fst.prodMk (continuous_toAdd.comp continuous_snd))
  have h2 : Continuous
      (fun p : tateGaloisGroup × tatePowerTwoProfiniteTateLevel n =>
        Multiplicative.ofAdd
          (tatePowerTwoLevelGaloisAction (n + 1) p.1
            (Multiplicative.toAdd p.2))) :=
    continuous_ofAdd.comp h
  have hfun : (fun p : tateGaloisGroup × tatePowerTwoProfiniteTateLevel n =>
        tatePowerTwoProfiniteLevelGaloisAction n p.1 p.2) =
      (fun p : tateGaloisGroup × tatePowerTwoProfiniteTateLevel n =>
        Multiplicative.ofAdd
          (tatePowerTwoLevelGaloisAction (n + 1) p.1
            (Multiplicative.toAdd p.2))) := by
    funext p
    exact tatePowerTwoProfiniteLevelGaloisAction_apply n p.1 p.2
  rw [hfun]
  exact h2

/-- The projection from the actual pro-2 limit is continuous. -/
theorem tateProfiniteLimitProjection_continuous (n : ℕ) :
    Continuous (fun x : tateProfiniteLimit => tateProfiniteLimitProjection n x) :=
  (tateProfiniteLimitProjection n).hom.2

/-- The family of all limit projections, viewed as a map into the product of the
finite levels. -/
noncomputable def tateProfiniteLimitProjectionFamily
    (x : tateProfiniteLimit) :
    (n : ℕ) → tatePowerTwoProfiniteTateLevel n :=
  fun n => tateProfiniteLimitProjection n x

/-- The projection family is continuous. -/
theorem tateProfiniteLimitProjectionFamily_continuous :
    Continuous tateProfiniteLimitProjectionFamily := by
  apply continuous_pi
  intro n
  exact tateProfiniteLimitProjection_continuous n

/-- The projection family is injective: the limit projections separate points of
the pro-2 Tate module. -/
theorem tateProfiniteLimitProjectionFamily_injective :
    Function.Injective tateProfiniteLimitProjectionFamily := by
  intro x y hxy
  apply LeanFormal.IUT.IUTII.Frobenioid.ProfiniteLimitTopology.profiniteLimitProjectionMap_injective
    tateProfiniteDiagram
  funext j
  cases j with
  | op n =>
    exact congrFun hxy n

/-- The projection family is a closed embedding of the pro-2 Tate module into
the product of its finite levels (continuous injective map from a compact space
to a Hausdorff space). -/
theorem tateProfiniteLimitProjectionFamily_isClosedEmbedding :
    Topology.IsClosedEmbedding tateProfiniteLimitProjectionFamily :=
  Continuous.isClosedEmbedding tateProfiniteLimitProjectionFamily_continuous
    tateProfiniteLimitProjectionFamily_injective

set_option maxHeartbeats 800000 in
/-- **Actual joint continuity of the limit action.**  The map
G_K x T_2 -> T_2 given by the actual action is continuous for the Krull
topology on G_K and the profinite topology on the pro-2 Tate module.  This is
derived from the finite-level continuity together with the closed embedding of
the pro-2 Tate module into the product of its finite levels. -/
theorem tateProfiniteLimitGaloisAction_continuous :
    Continuous
      (fun p : tateGaloisGroup × tateProfiniteLimit =>
        tateProfiniteLimitGaloisAction p.1 p.2) := by
  have he : Topology.IsEmbedding tateProfiniteLimitProjectionFamily :=
    tateProfiniteLimitProjectionFamily_isClosedEmbedding.isEmbedding
  apply (Topology.IsEmbedding.continuous_iff he).mpr
  have hfam : (tateProfiniteLimitProjectionFamily ∘
        (fun p : tateGaloisGroup × tateProfiniteLimit =>
          tateProfiniteLimitGaloisAction p.1 p.2)) =
      (fun p : tateGaloisGroup × tateProfiniteLimit => fun n : ℕ =>
        tateProfiniteLimitProjection n
          (tateProfiniteLimitGaloisAction p.1 p.2)) :=
    rfl
  rw [hfam]
  apply continuous_pi
  intro n
  have hproj : (fun p : tateGaloisGroup × tateProfiniteLimit =>
        tateProfiniteLimitProjection n
          (tateProfiniteLimitGaloisAction p.1 p.2)) =
      (fun p : tateGaloisGroup × tateProfiniteLimit =>
        tatePowerTwoProfiniteLevelGaloisAction n p.1
          (tateProfiniteLimitProjection n p.2)) := by
    funext p
    have h := congrArg
      (fun (g : tateProfiniteLimit ⟶ tatePowerTwoProfiniteTateLevel n) => g p.2)
      (tateProfiniteLimitGaloisAction_projection n p.1)
    simpa [ProfiniteGrp.comp_apply] using h
  rw [hproj]
  change Continuous
    ((fun q : tateGaloisGroup × tatePowerTwoProfiniteTateLevel n =>
        tatePowerTwoProfiniteLevelGaloisAction n q.1 q.2) ∘
      (fun p : tateGaloisGroup × tateProfiniteLimit =>
        (p.1, tateProfiniteLimitProjection n p.2)))
  have hfin : Continuous
      (fun q : tateGaloisGroup × tatePowerTwoProfiniteTateLevel n =>
        tatePowerTwoProfiniteLevelGaloisAction n q.1 q.2) :=
    tatePowerTwoProfiniteLevelGaloisAction_continuous n
  have hpair : Continuous
      (fun p : tateGaloisGroup × tateProfiniteLimit =>
        (p.1, tateProfiniteLimitProjection n p.2)) :=
    Continuous.prodMk continuous_fst
      ((tateProfiniteLimitProjection_continuous n).comp continuous_snd)
  exact hfin.comp hpair

end LimitJointContinuity

/-! ## The general-linear and matrix representations of the level action

The level action is `ZMod (2^(n+1))`-linear; this gives the basis-free
general-linear representation `G_K -> GL(E[2^(n+1)])`.  Relative to a
rank-two basis of the level this yields the actual matrix representation, with
the identity and composition laws and invertibility.  At the 2-torsion level a
rank-two basis is constructed from the actual points `(0,0)` and `(1,0)`, so
the matrix representation at level `E[2]` is unconditional.

The transition maps `[2] : E[2^(n+2)] -> E[2^(n+1)]` change the coefficient
ring, so there is no single matrix identity between the matrices at two
levels; the intrinsic compatibility is the already-proved commutation of the
level actions with the transitions
(`tatePowerTwoLevelGaloisAction_transition`). -/

/-- **Linearity of the level action.**  The automorphism of `E[2^(n+1)]`
induced by an absolute Galois element is `ZMod (2^(n+1))`-linear. -/
noncomputable def tatePowerTwoLevelGaloisLinearEquiv (n : Nat) (σ : tateGaloisGroup) :
    tatePowerTwoLevel (n + 1) ≃ₗ[ZMod (2 ^ (n + 1))] tatePowerTwoLevel (n + 1) :=
  { tatePowerTwoLevelGaloisAction (n + 1) σ with
    map_smul' := fun c P =>
      LeanFormal.IUT.ABCBridge.Galois.galoisTorsionEquiv_zmod_smul
        curveY2EqX3SubX (2 ^ (n + 1)) σ c P }

/-- The underlying additive equivalence of the linear level action is the
level action itself. -/
@[simp]
theorem tatePowerTwoLevelGaloisLinearEquiv_apply (n : Nat) (σ : tateGaloisGroup)
    (P : tatePowerTwoLevel (n + 1)) :
    tatePowerTwoLevelGaloisLinearEquiv n σ P =
      tatePowerTwoLevelGaloisAction (n + 1) σ P :=
  rfl

/-- **The general-linear representation.**  The absolute Galois group acts on
the `ZMod (2^(n+1))`-module `E[2^(n+1)]` by linear automorphisms. -/
noncomputable def tatePowerTwoLevelGaloisGeneralLinear (n : Nat) :
    tateGaloisGroup →*
      (tatePowerTwoLevel (n + 1) ≃ₗ[ZMod (2 ^ (n + 1))] tatePowerTwoLevel (n + 1)) where
  toFun := tatePowerTwoLevelGaloisLinearEquiv n
  map_one' := by
    apply LinearEquiv.ext
    intro P
    exact tatePowerTwoLevelGaloisAction_one_apply (n + 1) P
  map_mul' σ τ := by
    apply LinearEquiv.ext
    intro P
    exact tatePowerTwoLevelGaloisAction_mul_apply (n + 1) σ τ P

/-- The general-linear representation applied to a point is the level
action. -/
@[simp]
theorem tatePowerTwoLevelGaloisGeneralLinear_apply (n : Nat) (σ : tateGaloisGroup)
    (P : tatePowerTwoLevel (n + 1)) :
    tatePowerTwoLevelGaloisGeneralLinear n σ P =
      tatePowerTwoLevelGaloisAction (n + 1) σ P :=
  rfl

/-- **The matrix of the level action** relative to a rank-two basis of the
level `E[2^(n+1)]`. -/
noncomputable def tatePowerTwoLevelGaloisMatrix (n : Nat)
    (b : Module.Basis (Fin 2) (ZMod (2 ^ (n + 1))) (tatePowerTwoLevel (n + 1)))
    (σ : tateGaloisGroup) : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (n + 1))) :=
  LinearMap.toMatrix b b (tatePowerTwoLevelGaloisLinearEquiv n σ).toLinearMap

/-- The matrix of the identity element of the Galois group is the identity
matrix. -/
theorem tatePowerTwoLevelGaloisMatrix_one (n : Nat)
    (b : Module.Basis (Fin 2) (ZMod (2 ^ (n + 1))) (tatePowerTwoLevel (n + 1))) :
    tatePowerTwoLevelGaloisMatrix n b 1 = 1 := by
  unfold tatePowerTwoLevelGaloisMatrix
  have h : (tatePowerTwoLevelGaloisLinearEquiv n 1).toLinearMap = 1 := by
    apply LinearMap.ext
    intro P
    change tatePowerTwoLevelGaloisAction (n + 1) 1 P = P
    exact tatePowerTwoLevelGaloisAction_one_apply (n + 1) P
  rw [h, LinearMap.toMatrix_one]

/-- **The matrix representation is multiplicative.** -/
theorem tatePowerTwoLevelGaloisMatrix_mul (n : Nat)
    (b : Module.Basis (Fin 2) (ZMod (2 ^ (n + 1))) (tatePowerTwoLevel (n + 1)))
    (σ τ : tateGaloisGroup) :
    tatePowerTwoLevelGaloisMatrix n b (σ * τ) =
      tatePowerTwoLevelGaloisMatrix n b σ * tatePowerTwoLevelGaloisMatrix n b τ := by
  unfold tatePowerTwoLevelGaloisMatrix
  have h : (tatePowerTwoLevelGaloisLinearEquiv n (σ * τ)).toLinearMap =
      (tatePowerTwoLevelGaloisLinearEquiv n σ).toLinearMap.comp
        (tatePowerTwoLevelGaloisLinearEquiv n τ).toLinearMap := by
    apply LinearMap.ext
    intro P
    exact tatePowerTwoLevelGaloisAction_mul_apply (n + 1) σ τ P
  rw [h, ← Module.End.mul_eq_comp, LinearMap.toMatrix_mul]

/-- **Every level matrix is invertible.** -/
theorem tatePowerTwoLevelGaloisMatrix_isUnit (n : Nat)
    (b : Module.Basis (Fin 2) (ZMod (2 ^ (n + 1))) (tatePowerTwoLevel (n + 1)))
    (σ : tateGaloisGroup) :
    IsUnit (tatePowerTwoLevelGaloisMatrix n b σ) := by
  have h : tatePowerTwoLevelGaloisMatrix n b σ *
      tatePowerTwoLevelGaloisMatrix n b σ⁻¹ = 1 := by
    rw [← tatePowerTwoLevelGaloisMatrix_mul, mul_inv_cancel,
      tatePowerTwoLevelGaloisMatrix_one]
  have h' : tatePowerTwoLevelGaloisMatrix n b σ⁻¹ *
      tatePowerTwoLevelGaloisMatrix n b σ = 1 := by
    rw [← tatePowerTwoLevelGaloisMatrix_mul, inv_mul_cancel,
      tatePowerTwoLevelGaloisMatrix_one]
  exact isUnit_iff_exists.mpr ⟨_, h, h'⟩

/-! ## The actual rank-two basis of the 2-torsion level and its matrices -/

/-- The four-element exhaustion of the 2-torsion level by the explicit points. -/
theorem tateLevelTwo_cases (P : tateLevelTwoTorsion) :
    P = 0 ∨ P = tateLevelTwoPointZeroZero ∨ P = tateLevelTwoPointOneZero ∨
      P = tateLevelTwoPointMinusOneZero := by
  obtain ⟨i, hi⟩ := tateLevelTwoFourPoints_surjective P
  fin_cases i
  · left
    simp only [tateLevelTwoFourPoints] at hi
    exact hi.symm
  · right; left
    simp only [tateLevelTwoFourPoints] at hi
    exact hi.symm
  · right; right; left
    simp only [tateLevelTwoFourPoints] at hi
    exact hi.symm
  · right; right; right
    simp only [tateLevelTwoFourPoints] at hi
    exact hi.symm

/-- **The third 2-torsion point is the sum of the first two.** -/
theorem tateLevelTwoPointMinusOneZero_eq_add :
    tateLevelTwoPointMinusOneZero =
      tateLevelTwoPointZeroZero + tateLevelTwoPointOneZero := by
  have hQ2amb : (2 : Nat) • (tateLevelTwoPointOneZero : tateLevelFourPointType) = 0 :=
    tateLevelTwo_mem_iff.mp tateLevelTwoPointOneZero.2
  have hQ2 : tateLevelTwoPointOneZero + tateLevelTwoPointOneZero = 0 := by
    apply Subtype.ext
    simpa only [two_nsmul, AddSubgroup.coe_add, AddSubgroup.coe_zero] using hQ2amb
  have hnegQ : -tateLevelTwoPointOneZero = tateLevelTwoPointOneZero :=
    neg_eq_of_add_eq_zero_right hQ2
  have hneq0 : tateLevelTwoPointZeroZero + tateLevelTwoPointOneZero ≠ 0 := by
    intro h
    have hP : tateLevelTwoPointZeroZero = -tateLevelTwoPointOneZero :=
      eq_neg_of_add_eq_zero_left h
    rw [hnegQ] at hP
    exact tateLevelTwoPointZeroZero_ne_oneZero hP
  have hneqP : tateLevelTwoPointZeroZero + tateLevelTwoPointOneZero ≠
      tateLevelTwoPointZeroZero := by
    intro h
    have := add_left_cancel (h.trans (add_zero tateLevelTwoPointZeroZero).symm)
    exact tateLevelTwoPointOneZero_ne_zero this
  have hneqQ : tateLevelTwoPointZeroZero + tateLevelTwoPointOneZero ≠
      tateLevelTwoPointOneZero := by
    intro h
    have := add_right_cancel (h.trans (zero_add tateLevelTwoPointOneZero).symm)
    exact tateLevelTwoPointZeroZero_ne_zero this
  rcases tateLevelTwo_cases (tateLevelTwoPointZeroZero + tateLevelTwoPointOneZero) with
    h | h | h | h
  · exact absurd h hneq0
  · exact absurd h hneqP
  · exact absurd h hneqQ
  · exact h.symm

/-- The coordinate linear map spanned by the 2-torsion points `(0,0)` and
`(1,0)` in the `ZMod 2`-module `E[2]`. -/
noncomputable def tateLevelTwoCoordinateMap :
    (Fin 2 → ZMod 2) →ₗ[ZMod 2] tateLevelTwoTorsion where
  toFun x := x 0 • tateLevelTwoPointZeroZero + x 1 • tateLevelTwoPointOneZero
  map_add' x y := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_add, smul_smul, RingHom.id_apply, smul_eq_mul]

/-- The coordinate map in coordinates. -/
theorem tateLevelTwoCoordinateMap_apply (x : Fin 2 → ZMod 2) :
    tateLevelTwoCoordinateMap x =
      x 0 • tateLevelTwoPointZeroZero + x 1 • tateLevelTwoPointOneZero :=
  rfl

theorem zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : a.val < 2 := ZMod.val_lt a
  have h' : a.val = 0 ∨ a.val = 1 := by omega
  rcases h' with h0 | h1
  · left; rw [← ZMod.natCast_zmod_val a, h0]; simp
  · right; rw [← ZMod.natCast_zmod_val a, h1]; norm_num

/-- **Injectivity of the coordinate map.** -/
theorem tateLevelTwoCoordinateMap_injective :
    Function.Injective tateLevelTwoCoordinateMap := by
  rw [← LinearMap.ker_eq_bot]
  ext x
  simp only [LinearMap.mem_ker, AddSubgroup.mem_bot]
  constructor
  · intro hx
    rcases zmod_two_eq_zero_or_one (x 0) with h0 | h0 <;>
      rcases zmod_two_eq_zero_or_one (x 1) with h1 | h1
    · funext i
      fin_cases i
      · simpa using h0
      · simpa using h1
    · exfalso
      have h : tateLevelTwoPointOneZero = 0 := by
        have h' := hx
        rw [tateLevelTwoCoordinateMap_apply, h0, h1] at h'
        simpa using h'
      exact tateLevelTwoPointOneZero_ne_zero h
    · exfalso
      have h : tateLevelTwoPointZeroZero = 0 := by
        have h' := hx
        rw [tateLevelTwoCoordinateMap_apply, h0, h1] at h'
        simpa using h'
      exact tateLevelTwoPointZeroZero_ne_zero h
    · exfalso
      have hsum : tateLevelTwoPointZeroZero + tateLevelTwoPointOneZero = 0 := by
        have h' := hx
        rw [tateLevelTwoCoordinateMap_apply, h0, h1] at h'
        simpa using h'
      have hPQ : tateLevelTwoPointZeroZero = tateLevelTwoPointOneZero := by
        have hneg := eq_neg_of_add_eq_zero_left hsum
        have hQ2amb : (2 : Nat) •
            (tateLevelTwoPointOneZero : tateLevelFourPointType) = 0 :=
          tateLevelTwo_mem_iff.mp tateLevelTwoPointOneZero.2
        have hQ2 : tateLevelTwoPointOneZero + tateLevelTwoPointOneZero = 0 := by
          apply Subtype.ext
          simpa only [two_nsmul, AddSubgroup.coe_add, AddSubgroup.coe_zero] using hQ2amb
        have hnegQ : -tateLevelTwoPointOneZero = tateLevelTwoPointOneZero :=
          neg_eq_of_add_eq_zero_right hQ2
        rw [hnegQ] at hneg
        exact hneg
      exact tateLevelTwoPointZeroZero_ne_oneZero hPQ
  · intro hx
    rw [hx]
    simp

/-- **Surjectivity of the coordinate map.** -/
theorem tateLevelTwoCoordinateMap_surjective :
    Function.Surjective tateLevelTwoCoordinateMap := by
  intro P
  have hR : tateLevelTwoPointMinusOneZero =
      tateLevelTwoPointZeroZero + tateLevelTwoPointOneZero :=
    tateLevelTwoPointMinusOneZero_eq_add
  rcases tateLevelTwo_cases P with h | h | h | h
  · refine ⟨0, ?_⟩
    rw [h]
    simp [tateLevelTwoCoordinateMap_apply]
  · refine ⟨![1, 0], ?_⟩
    rw [h]
    simp [tateLevelTwoCoordinateMap_apply]
  · refine ⟨![0, 1], ?_⟩
    rw [h]
    simp [tateLevelTwoCoordinateMap_apply]
  · refine ⟨![1, 1], ?_⟩
    rw [h, hR]
    simp [tateLevelTwoCoordinateMap_apply]

/-- The coordinate linear equivalence `(ZMod 2)^2 ~= E[2]`. -/
noncomputable def tateLevelTwoCoordinateEquiv :
    (Fin 2 → ZMod 2) ≃ₗ[ZMod 2] tateLevelTwoTorsion where
  toFun := tateLevelTwoCoordinateMap
  map_add' := tateLevelTwoCoordinateMap.map_add
  map_smul' := tateLevelTwoCoordinateMap.map_smul
  invFun := Function.invFun tateLevelTwoCoordinateMap
  left_inv := Function.leftInverse_invFun tateLevelTwoCoordinateMap_injective
  right_inv := Function.rightInverse_invFun tateLevelTwoCoordinateMap_surjective

/-- **The actual rank-two basis of the 2-torsion level** `E[2]`, with first
vector `(0,0)` and second vector `(1,0)`. -/
noncomputable def tateLevelTwoBasis : Module.Basis (Fin 2) (ZMod 2) tateLevelTwoTorsion :=
  (Pi.basisFun (ZMod 2) (Fin 2)).map tateLevelTwoCoordinateEquiv

/-- **The actual `2 x 2` matrix of the absolute Galois action on `E[2]`.** -/
noncomputable def tateLevelTwoGaloisMatrix (σ : tateGaloisGroup) :
    Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  tatePowerTwoLevelGaloisMatrix 0
    (show Module.Basis (Fin 2) (ZMod (2 ^ (0 + 1))) (tatePowerTwoLevel (0 + 1)) from
      tateLevelTwoBasis) σ

/-- The `2 x 2` matrices at level `E[2]` form a multiplicative matrix
representation of the absolute Galois group. -/
theorem tateLevelTwoGaloisMatrix_mul (σ τ : tateGaloisGroup) :
    tateLevelTwoGaloisMatrix (σ * τ) =
      tateLevelTwoGaloisMatrix σ * tateLevelTwoGaloisMatrix τ :=
  tatePowerTwoLevelGaloisMatrix_mul 0 _ σ τ

/-- The `2 x 2` matrix of the identity is the identity matrix. -/
theorem tateLevelTwoGaloisMatrix_one : tateLevelTwoGaloisMatrix 1 = 1 :=
  tatePowerTwoLevelGaloisMatrix_one 0 _

/-- Every `2 x 2` matrix at level `E[2]` is invertible. -/
theorem tateLevelTwoGaloisMatrix_isUnit (σ : tateGaloisGroup) :
    IsUnit (tateLevelTwoGaloisMatrix σ) :=
  tatePowerTwoLevelGaloisMatrix_isUnit 0 _ σ

/-! ## The packaged actual pro-2 Tate module with its G_K action -/

/-- The actual pro-2 Tate module of y^2 = x^3 - x together with the actual
level actions of the absolute Galois group, compatible with the transition maps,
and the actual limit action, compatible with the projections, with the identity
and composition laws, and with the level transition compatibility. -/
structure ProTwoTateGaloisModule where
  /-- The finite levels E[2^(n+1)]. -/
  level : ℕ → ProfiniteGrp
  /-- The transition maps [2]. -/
  transition : ∀ n : ℕ, level (n + 1) ⟶ level n
  /-- The pro-2 Tate module T_2(E). -/
  tateModule : ProfiniteGrp
  /-- The projections from the limit. -/
  projection : ∀ n : ℕ, tateModule ⟶ level n
  /-- The projections are compatible with the transitions. -/
  projection_compat : ∀ n : ℕ, projection (n + 1) ≫ transition n = projection n
  /-- The action on the finite levels. -/
  levelAction : ∀ n : ℕ, tateGaloisGroup → (level n ⟶ level n)
  /-- The level actions commute with the transitions. -/
  levelAction_transition : ∀ (n : ℕ) (σ : tateGaloisGroup),
    transition n ≫ levelAction n σ = levelAction (n + 1) σ ≫ transition n
  /-- The action on the limit. -/
  limitAction : tateGaloisGroup → (tateModule ⟶ tateModule)
  /-- The limit action commutes with the projections. -/
  limitAction_projection : ∀ (n : ℕ) (σ : tateGaloisGroup),
    limitAction σ ≫ projection n = projection n ≫ levelAction n σ
  /-- The identity acts trivially. -/
  limitAction_one : limitAction 1 = 𝟙 tateModule
  /-- The composition law. -/
  limitAction_mul : ∀ σ τ : tateGaloisGroup,
    limitAction (σ * τ) = limitAction τ ≫ limitAction σ
  /-- The limit action is continuous in both variables for the Krull topology
  on the Galois group and the profinite topology on the Tate module. -/
  limitAction_continuous : Continuous
    (fun p : tateGaloisGroup × tateModule => limitAction p.1 p.2)

/-- **The actual pro-2 Tate module with its actual G_K action.** -/
noncomputable def actualProTwoTateGaloisModule : ProTwoTateGaloisModule where
  level := tatePowerTwoProfiniteTateLevel
  transition := tatePowerTwoProfiniteTransition
  tateModule := tateProfiniteLimit
  projection := tateProfiniteLimitProjection
  projection_compat := tatePowerTwoProfiniteLimitProjection_compatible
  levelAction := tatePowerTwoProfiniteLevelGaloisAction
  levelAction_transition := tatePowerTwoProfiniteLevelGaloisAction_transition
  limitAction := tateProfiniteLimitGaloisAction
  limitAction_projection := tateProfiniteLimitGaloisAction_projection
  limitAction_one := tateProfiniteLimitGaloisAction_one
  limitAction_mul := tateProfiniteLimitGaloisAction_mul
  limitAction_continuous := tateProfiniteLimitGaloisAction_continuous

/-- The only frozen card: the full arithmetic Tate module prod_l T_l(E) together
with the source curve pi identification.  Both are existing source cards; this
file neither constructs nor claims them. -/
def fullTateAndSourceIdentificationCard : Prop :=
  LeanFormal.IUT.IUTII.Frobenioid.Example36.TateModuleProfinite.FullProductTateModuleCard ∧
    SourceCurvePiCard

end TateGaloisAction
end Example36
end LeanFormal.IUT.IUTII.Frobenioid
