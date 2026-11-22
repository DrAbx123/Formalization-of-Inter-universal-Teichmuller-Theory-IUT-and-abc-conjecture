/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal IUT/ABC contributors
-/
import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripBridge
import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripDivisorFrobenius
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianLocalGalois
import LeanFormal.IUT.IUTII.Frobenioid.Example36ArchimedeanLocal
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtalePiOneKernelRealization
import LeanFormal.IUT.IUTII.Frobenioid.Example36EllipticCurveAnabelioid
import LeanFormal.IUT.IUTII.Frobenioid.Example36EllipticCurveTateHigherLevel
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
/-!
# Actual prime-strip components at the places of a number field

This module constructs the local prime-strip components Pi_v and Mon_v at the
finite and infinite places of a number field out of the actual local arithmetic
data, and proves the value/degree/realification/Frobenius identifications with
the Example 3.6 backend.  It is the Layer-1 handoff Ch1 section J4 construction.

## The components

The place index is NumberFieldPlaceIndex = HeightOneSpectrum (ringOfIntegers F) sum InfinitePlace F.

* At a finite place v, the local field is the actual v-adic completion
  v.adicCompletion F.  The group Pi_v (and the mono-analytic group G_v) is
  the actual local absolute Galois group AbsoluteGaloisProfinite (v.adicCompletion F);
  the projection is the identity.  The value monoid Mon_v is the unit group of
  the completion.  The degree is the normalized local log-volume
  -nu_v(x) * log #(O_F / v), constructed from the actual completion exponent
  and residue-field cardinality.  The Galois action on the base local-field units
  is the trivial one; this is a genuine action, since the local Galois group fixes
  the base local field elementwise.
* At an infinite place w, the local field is the actual completion
  w.Completion.  The group Pi_v = G_v is its local absolute Galois group and
  the projection is the identity.  The monoid Mon_v is the unit-level lift: the
  unit group of the completion.  Its degree is -log ||x||_w, the actual
  archimedean log-volume; this degree is the value-group coordinate, and the
  backend archimedean value group is its image.  The identification with the
  backend value-group component is therefore proved on principal values (global
  units), not asserted as an isomorphism of the unit monoid with the value group.

The components are packaged in PrimeStripComponent and assembled into the
place-indexed numberFieldPrimeStrip : FPrimeStrip NumberFieldPlaceIndex.

## Identification with the source model/backend

The following identifications are proved from the actual constructions, not
assumed:

* finite place: finitePlacePrimeStripComponent_degree_eq_backend identifies
  the component degree with the backend finitePlaceLocalDegree;
  finitePlacePrimeStripComponent_degree_eq_valueGroupDegree_comp identifies it
  with the backend value-group degree composed with the actual value map
  finitePlaceLocalValue; finitePlacePrimeStripValueMap_surjective and
  finitePlacePrimeStripValueMap_ker identify the value map with the quotient of
  the completion units by the integral units O_v^x;
  finitePlaceValueKernel_realification_eq_unitValueKernel identifies the
  component realification with the backend finitePlaceUnitValueKernel;
  finitePlaceValueKernel_realification_globalUnit and
  finitePlaceValueKernel_realification_eq_backendDivisor identify the
  realification of an embedded global unit with the Example 3.6 packaged
  finite-place coordinate and with the finite coordinate of the actual
  model-Frobenioid divisor input.
* infinite place: infinitePlaceValueKernel_realification_globalUnit identifies
  the realification of an embedded global unit with the Example 3.6
  infiniteDelta; infinitePlaceValueKernel_realification_eq_backendDivisor
  identifies it with the archimedean coordinate of the model-Frobenioid divisor
  input; infinitePlacePrimeStripComponent_degree_globalUnit_eq_archimedeanValueUnit
  identifies the component degree with the backend archimedeanPlaceValueUnit.
* degree kernels: finitePlaceValueKernel_degree_eq_one_iff proves that the
  finite-place degree kernel is exactly the group of integral units, and
  infinitePlaceValueKernel_degree_eq_one_iff proves that the archimedean degree
  kernel is exactly the norm-one unit group.
* Frobenius: finitePlaceValueKernel_degree_valueFrobeniusPower,
  infinitePlaceValueKernel_degree_valueFrobeniusPower,
  finitePlaceValueKernel_realification_pow,
  infinitePlaceValueKernel_realification_pow, and the global-unit power theorems
  prove the degree/realification laws for the value-side Frobenius dynamics
  valueFrobeniusPower; finitePlaceValueKernel_realification_eq_divisorRealification
  and infinitePlaceValueKernel_realification_eq_divisorRealification identify
  the component realifications with the divisor-side realifications of
  Example36PrimeStripDivisorFrobenius.

## Boundary: the exact missing source component

The source F-prime-strip of IUT uses, at a place, the tempered/etale fundamental
group of a once-punctured elliptic curve over the local field, with a surjection
onto the local absolute Galois group whose kernel is the geometric fundamental
group, together with the resulting action on the local value monoid.  The present
module constructs the arithmetic local Galois group, not that curve fundamental
group.  Consequently the geometric kernel of the constructed arithmetic
component is trivial (numberFieldPrimeStrip_geometric_finite and
numberFieldPrimeStrip_geometric_infinite).  The exact missing component is the
actual once-punctured elliptic curve over the local field, its tempered/etale
fundamental group Pi_v, the projection to G_v with nontrivial geometric kernel,
and the nontrivial action of Pi_v on the local value monoid with degree
compatibility.  Mathlib 4.32.2 provides no etale fundamental group of a curve and
no curve-to-anabelioid functor, so this component is not constructed here and no
structure card or unproved placeholder is used as a substitute.  The value/degree/realification
and Frobenius identifications above are unconditional theorems about the
arithmetic components.

## Additions (Layer-1 build, 2026-10-20): actual Tate-module affine strips

The arithmetic components above have trivial geometric kernels.  This module now
also constructs, from the concrete curve `y^2 = x^3 - x` of
Example36EllipticCurveAnabelioid/TateHigherLevel, the semidirect (affine)
D-prime-strips whose geometric kernel is the *actual* Tate layer and on which the
*actual* Galois action operates:

* tateLevelTwoGaloisActionHom / tateLevelFourGaloisActionHom are the Galois
  actions on `E[2]` and `E[4]` as monoid homomorphisms into the automorphism
  groups of the Tate layers, built from `galoisTorsionEquiv`;
* tateLevelTwoAffineDPrimeStrip and tateLevelFourAffineDPrimeStrip are the
  affine strips `E[2^n] ⋊ Gal(Qbar/Q)`, with arithmetic group the actual
  absolute Galois group of `Q` (tateLevelTwoAffineDPrimeStrip_G_eq_absoluteGalois)
  and geometric kernels multiplicatively equivalent to the concrete `E[2]` and
  `E[4]` (tateLevelTwoAffineDPrimeStrip_geometricMulEquiv,
  tateLevelFourAffineDPrimeStrip_geometricMulEquiv);
* the level-two kernel is nontrivial with an explicit element coming from the
  concrete point `(0,0)`, and has exactly four elements
  (tateLevelTwoAffineDPrimeStrip_geometric_card); the level-four kernel is
  nontrivial with the same explicit point
  (tateLevelFourAffineDPrimeStrip_geometric_ne_bot);
* tateLevelTwoAffine_conj_eq_galoisAction proves that conjugation by the
  arithmetic part is exactly the actual Galois action on the kernel: the
  geometric kernel is the actual Galois module, not an unrelated second group;
* tateLevelTwoAffine_fiberOrbit_subsingleton proves that the explicit orbit
  relation of the affine action on the geometric fiber has a single class, i.e.
  the fiber is a torsor and its mono-analytic quotient is a point.

Component identification with the divisor side:
finitePlacePrimeStripComponent_degree_eq_finiteDivisorKernel and
infinitePlacePrimeStripComponent_degree_eq_archimedeanDivisorKernel identify the
component degree of an embedded global unit with the realification of the actual
Example 3.6 divisor kernel on the principal divisor;
finitePlacePrimeStripComponent_degree_pow_eq_divisorFrobenius identifies the
degree of `f^n` with the divisor-side degree-`n` Frobenius action.

The exact missing component is recorded as the proposition
SourceCurveGeometricComponent (a nontrivial group multiplicatively equivalent to
the geometric kernel at a place), which is proved to imply a nontrivial kernel
(hasNontrivialGeometricComponentAt_of_sourceCurve); the arithmetic number-field
strip is proved not to satisfy it at any place
(numberFieldPrimeStrip_not_hasNontrivialGeometricComponentAt), while the
level-two affine strip does
(tateLevelTwoAffine_hasNontrivialGeometricComponentAt).

Boundary of these additions (honest): the affine total groups are plain groups,
not profinite groups; continuity of the Galois action on the Tate layers with
respect to the Krull topology is not formalized, so no `B(G)` anabelioid is
attached to the affine total group.  The Galois equivariance of the level
transition `E[4] -> E[2]` and the pro-2 inverse limit `T_2(E) = lim E[2^n]` are
not constructed.  The geometric kernels realized are the finite abelian Tate
layers of the proper elliptic curve, not the nonabelian fundamental group of the
once-punctured curve, and no free-profinite-of-rank-two group, cusp inertia or
curve anabelioid is constructed.

No theta-pilot, q-pilot, Tate uniformization, or source Hodge theater is
constructed or claimed.
-/

noncomputable section
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.IUTII.Frobenioid.Example36

open IsDedekindDomain NumberField
open scoped NumberField
open LeanFormal.IUT
open Iut

universe u

variable {F : Type u} [Field F] [NumberField F]

abbrev NumberFieldPlaceIndex : Type u :=
  HeightOneSpectrum (𝓞 F) ⊕ NumberField.InfinitePlace F

abbrev finitePlaceLocalField (v : HeightOneSpectrum (𝓞 F)) : Type u :=
  v.adicCompletion F

abbrev infinitePlaceLocalField (w : NumberField.InfinitePlace F) : Type u :=
  w.Completion

abbrev placeLocalField (P : NumberFieldPlaceIndex (F := F)) : Type u :=
  match P with
  | Sum.inl v => finitePlaceLocalField (F := F) v
  | Sum.inr w => infinitePlaceLocalField (F := F) w

def placeGalois (P : NumberFieldPlaceIndex (F := F)) : ProfiniteGrp.{u} :=
  match P with
  | Sum.inl v => AbsoluteGaloisProfinite (finitePlaceLocalField (F := F) v)
  | Sum.inr w => AbsoluteGaloisProfinite (infinitePlaceLocalField (F := F) w)

abbrev placePi (P : NumberFieldPlaceIndex (F := F)) : Type u := placeGalois (F := F) P

def finitePlaceCompletionDegree (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ →* Multiplicative ℝ where
  toFun x := Multiplicative.ofAdd
    (-(completionValuationExponent v x : ℝ) *
      Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)))
  map_one' := by simp
  map_mul' := by
    intro x y
    rw [completionValuationExponent_mul]
    push_cast
    rw [← ofAdd_add]
    congr 1
    ring

@[simp] theorem finitePlaceCompletionDegree_apply
    (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    finitePlaceCompletionDegree (F := F) v x = Multiplicative.ofAdd
      (-(completionValuationExponent v x : ℝ) *
        Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ))) := by
  simp [finitePlaceCompletionDegree]

theorem finitePlaceCompletionDegree_eq_localDegree
    (v : HeightOneSpectrum (𝓞 F)) :
    finitePlaceCompletionDegree (F := F) v = finitePlaceLocalDegree (F := F) v := by
  ext x
  rw [finitePlaceCompletionDegree_apply, finitePlaceLocalDegree_apply]

def infinitePlaceCompletionDegree (w : NumberField.InfinitePlace F) :
    (w.Completion)ˣ →* Multiplicative ℝ where
  toFun u := Multiplicative.ofAdd (-Real.log ‖(u : w.Completion)‖)
  map_one' := by simp
  map_mul' := by
    intro u v
    change Multiplicative.ofAdd (-Real.log ‖((u * v : (w.Completion)ˣ) : w.Completion)‖) =
      Multiplicative.ofAdd (-Real.log ‖(u : w.Completion)‖) *
        Multiplicative.ofAdd (-Real.log ‖(v : w.Completion)‖)
    rw [Units.val_mul, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr (Units.ne_zero u))
        (norm_ne_zero_iff.mpr (Units.ne_zero v))]
    rw [← ofAdd_add]
    congr 1
    ring

structure PrimeStripComponent where
  Pi : Type u
  groupPi : Group Pi
  G : Type u
  groupG : Group G
  proj : Pi →* G
  proj_surjective : Function.Surjective proj
  Mon : Type u
  commMonoidMon : CommMonoid Mon
  action : Pi →* MulAut Mon
  degree : Mon →* Multiplicative ℝ

attribute [instance] PrimeStripComponent.groupPi PrimeStripComponent.groupG
  PrimeStripComponent.commMonoidMon

noncomputable def finitePlacePrimeStripComponent (v : HeightOneSpectrum (𝓞 F)) :
    PrimeStripComponent.{u} where
  Pi := AbsoluteGaloisProfinite (v.adicCompletion F)
  groupPi := inferInstance
  G := AbsoluteGaloisProfinite (v.adicCompletion F)
  groupG := inferInstance
  proj := MonoidHom.id _
  proj_surjective := Function.surjective_id
  Mon := (v.adicCompletion F)ˣ
  commMonoidMon := inferInstance
  action := 1
  degree := finitePlaceCompletionDegree (F := F) v

noncomputable def infinitePlacePrimeStripComponent (w : NumberField.InfinitePlace F) :
    PrimeStripComponent.{u} where
  Pi := AbsoluteGaloisProfinite (w.Completion)
  groupPi := inferInstance
  G := AbsoluteGaloisProfinite (w.Completion)
  groupG := inferInstance
  proj := MonoidHom.id _
  proj_surjective := Function.surjective_id
  Mon := (w.Completion)ˣ
  commMonoidMon := inferInstance
  action := 1
  degree := infinitePlaceCompletionDegree (F := F) w

noncomputable def finitePlaceValueKernel (v : HeightOneSpectrum (𝓞 F)) :
    FrobenioidValueKernel ((finitePlacePrimeStripComponent (F := F) v).Mon) where
  degree := (finitePlacePrimeStripComponent (F := F) v).degree
  realification := fun x => Multiplicative.toAdd ((finitePlacePrimeStripComponent (F := F) v).degree x)
  realification_mul := by
    intro x y
    rw [map_mul, toAdd_mul]
  degree_realification := by
    intro x
    rfl
  unit := 1
  unit_realification := by simp
  effective := fun _ => True
  effective_proved := fun _ => trivial
  transport := id
  transport_degree := by intro x; simp

noncomputable def infinitePlaceValueKernel (w : NumberField.InfinitePlace F) :
    FrobenioidValueKernel ((infinitePlacePrimeStripComponent (F := F) w).Mon) where
  degree := (infinitePlacePrimeStripComponent (F := F) w).degree
  realification := fun x => Multiplicative.toAdd ((infinitePlacePrimeStripComponent (F := F) w).degree x)
  realification_mul := by
    intro x y
    rw [map_mul, toAdd_mul]
  degree_realification := by
    intro x
    rfl
  unit := 1
  unit_realification := by simp
  effective := fun _ => True
  effective_proved := fun _ => trivial
  transport := id
  transport_degree := by intro x; simp

theorem finitePlacePrimeStripComponent_degree_eq_backend (v : HeightOneSpectrum (𝓞 F)) :
    (finitePlacePrimeStripComponent (F := F) v).degree =
      finitePlaceLocalDegree (F := F) v := by
  change finitePlaceCompletionDegree (F := F) v = finitePlaceLocalDegree (F := F) v
  exact finitePlaceCompletionDegree_eq_localDegree (F := F) v


theorem finitePlacePrimeStripComponent_degree_eq_valueGroupDegree_comp
    (v : HeightOneSpectrum (𝓞 F)) :
    (finitePlacePrimeStripComponent (F := F) v).degree =
      (finitePlaceValueGroupDegree (F := F) v).comp
        (finitePlaceLocalValue (F := F) v) := by
  rw [finitePlacePrimeStripComponent_degree_eq_backend,
    finitePlaceLocalDegree_factorization]

theorem finitePlacePrimeStripComponent_degree_globalUnit_eq_valueGroupDegree
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (finitePlacePrimeStripComponent (F := F) v).degree
        (finitePlaceGlobalUnitValue (F := F) v f) =
      finitePlaceValueGroupDegree (F := F) v
        (finitePlaceLocalValue (F := F) v
          (finitePlaceGlobalUnitValue (F := F) v f)) := by
  rw [finitePlacePrimeStripComponent_degree_eq_valueGroupDegree_comp]
  exact MonoidHom.comp_apply _ _ _

theorem infinitePlacePrimeStripComponent_degree_globalUnit_eq_archimedeanValueUnit
    (w : NumberField.InfinitePlace F) (f : Fˣ) :
    (infinitePlacePrimeStripComponent (F := F) w).degree
        (Units.map (algebraMap F w.Completion).toMonoidHom f) =
      archimedeanPlaceValueUnit (F := F) w f := by
  change infinitePlaceCompletionDegree (F := F) w
      (Units.map (algebraMap F w.Completion).toMonoidHom f) = _
  apply Multiplicative.ext
  change -Real.log ‖((Units.map (algebraMap F w.Completion).toMonoidHom f :
      (w.Completion)ˣ) : w.Completion)‖ = archimedeanPlaceValue w f
  have hnorm : ‖((Units.map (algebraMap F w.Completion).toMonoidHom f :
      (w.Completion)ˣ) : w.Completion)‖ = w (f : F) := by
    change ‖algebraMap F w.Completion (f : F)‖ = w (f : F)
    rw [NumberField.InfinitePlace.Completion.algebraMap_apply,
      NumberField.InfinitePlace.Completion.norm_coe]
    simp
  rw [hnorm]
  simp [archimedeanPlaceValue]

theorem infinitePlacePrimeStripComponent_degree_eq_backend
    (w : NumberField.InfinitePlace F) :
    (infinitePlacePrimeStripComponent (F := F) w).degree =
      infinitePlaceCompletionDegree (F := F) w := by
  ext x
  simp [infinitePlacePrimeStripComponent]

theorem finitePlaceValueKernel_realification_globalUnit
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (finitePlaceValueKernel (F := F) v).realification
        (finitePlaceGlobalUnitValue (F := F) v f) =
      -((numberFieldGlobalPlaceData (F := F)).finiteDelta f v : ℝ) *
        Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) := by
  change Multiplicative.toAdd (finitePlaceCompletionDegree (F := F) v
      (finitePlaceGlobalUnitValue (F := F) v f)) = _
  rw [finitePlaceCompletionDegree_eq_localDegree, finitePlaceLocalDegree_apply,
    finitePlaceGlobalUnitValue_exponent, ← numberFieldGlobalPlaceData_finiteDelta]
  simp

theorem infinitePlaceValueKernel_realification_globalUnit
    (w : NumberField.InfinitePlace F) (f : Fˣ) :
    (infinitePlaceValueKernel (F := F) w).realification
        (Units.map (algebraMap F w.Completion).toMonoidHom f) =
      (numberFieldGlobalPlaceData (F := F)).infiniteDelta f w := by
  change -Real.log ‖((Units.map (algebraMap F w.Completion).toMonoidHom f :
      (w.Completion)ˣ) : w.Completion)‖ = _
  have hnorm : ‖((Units.map (algebraMap F w.Completion).toMonoidHom f :
      (w.Completion)ˣ) : w.Completion)‖ = w (f : F) := by
    change ‖algebraMap F w.Completion (f : F)‖ = w (f : F)
    rw [NumberField.InfinitePlace.Completion.algebraMap_apply,
      NumberField.InfinitePlace.Completion.norm_coe]
    simp
  rw [hnorm, numberFieldGlobalPlaceData_infiniteDelta]

theorem finitePlaceValueKernel_degree_eq_one_iff
    (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    (finitePlaceValueKernel (F := F) v).degree x = 1 ↔
      x ∈ (v.adicCompletionIntegers F).units := by
  change finitePlaceCompletionDegree (F := F) v x = 1 ↔ _
  rw [finitePlaceCompletionDegree_eq_localDegree]
  exact finitePlaceUnitValueKernel_degree_eq_one_iff_mem_integralUnits (F := F) v x

theorem infinitePlaceValueKernel_degree_eq_one_iff
    (w : NumberField.InfinitePlace F) (x : (w.Completion)ˣ) :
    (infinitePlaceValueKernel (F := F) w).degree x = 1 ↔
      ‖(x : w.Completion)‖ = 1 := by
  change infinitePlaceCompletionDegree (F := F) w x = 1 ↔ _
  rw [infinitePlaceCompletionDegree]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  rw [ofAdd_eq_one, neg_eq_zero]
  constructor
  · intro h
    have hpos : 0 < ‖(x : w.Completion)‖ := norm_pos_unit (w.Completion) x
    rcases Real.log_eq_zero.mp h with h0 | h1 | hneg
    · exact absurd h0 (ne_of_gt hpos)
    · exact h1
    · nlinarith
  · intro h
    rw [h]
    simp

theorem finitePlaceValueKernel_realification_pow
    (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) (n : ℕ) :
    (finitePlaceValueKernel (F := F) v).realification (x ^ n) =
      (n : ℝ) * (finitePlaceValueKernel (F := F) v).realification x :=
  valueFrobeniusPower_realification (finitePlaceValueKernel (F := F) v) x n

theorem infinitePlaceValueKernel_realification_pow
    (w : NumberField.InfinitePlace F) (x : (w.Completion)ˣ) (n : ℕ) :
    (infinitePlaceValueKernel (F := F) w).realification (x ^ n) =
      (n : ℝ) * (infinitePlaceValueKernel (F := F) w).realification x :=
  valueFrobeniusPower_realification (infinitePlaceValueKernel (F := F) w) x n

theorem finitePlaceValueKernel_degree_valueFrobeniusPower
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ+) (x : (v.adicCompletion F)ˣ) :
    (finitePlaceValueKernel (F := F) v).degree (valueFrobeniusPower n x) =
      ((finitePlaceValueKernel (F := F) v).degree x) ^ (n : ℕ) :=
  valueFrobeniusPower_degree (finitePlaceValueKernel (F := F) v) n x

theorem infinitePlaceValueKernel_degree_valueFrobeniusPower
    (w : NumberField.InfinitePlace F) (n : ℕ+) (x : (w.Completion)ˣ) :
    (infinitePlaceValueKernel (F := F) w).degree (valueFrobeniusPower n x) =
      ((infinitePlaceValueKernel (F := F) w).degree x) ^ (n : ℕ) :=
  valueFrobeniusPower_degree (infinitePlaceValueKernel (F := F) w) n x



theorem finitePlaceValueKernel_realification_eq_unitValueKernel
    (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    (finitePlaceValueKernel (F := F) v).realification x =
      (finitePlaceUnitValueKernel (F := F) v).realification x := by
  change Multiplicative.toAdd (finitePlaceCompletionDegree (F := F) v x) = _
  rw [finitePlaceCompletionDegree_eq_localDegree,
    finitePlaceUnitValueKernel_realification, finitePlaceLocalDegree_apply]
  simp


theorem sourceModelInput_divisor_fst_eq_finiteExponent_apply
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (SourceModelBackend.coneGrothendieckEquiv (F := F)
      ((SourceModelBackend.numberFieldSourceModelInput (F := F)).divisor
        SourceModelBackend.bottomPoint (Additive.ofMul f))).1 v =
      finitePlaceValueExponent v f := by
  change (SourceModelBackend.coneComparison (F := F)
    ((SourceModelBackend.numberFieldSourceModelInput (F := F)).divisor
      SourceModelBackend.bottomPoint (Additive.ofMul f))).1 v =
    finitePlaceValueExponent v f
  exact SourceModelBackendDocking.sourceModelInput_divisor_fst_eq_finiteExponent
    (F := F) (Additive.ofMul f) v

theorem sourceModelInput_divisor_snd_eq_archimedeanValue_apply
    (w : NumberField.InfinitePlace F) (f : Fˣ) :
    (SourceModelBackend.coneGrothendieckEquiv (F := F)
      ((SourceModelBackend.numberFieldSourceModelInput (F := F)).divisor
        SourceModelBackend.bottomPoint (Additive.ofMul f))).2 w =
      archimedeanPlaceValue w f := by
  change (SourceModelBackend.coneComparison (F := F)
    ((SourceModelBackend.numberFieldSourceModelInput (F := F)).divisor
      SourceModelBackend.bottomPoint (Additive.ofMul f))).2 w =
    archimedeanPlaceValue w f
  exact SourceModelBackendDocking.sourceModelInput_divisor_snd_eq_archimedeanValue
    (F := F) (Additive.ofMul f) w

theorem principalDivisorExplicit_fst_apply
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)).1 v =
      finitePlaceValueExponent v f := by
  simpa using SourceModelBackendDocking.principalDivisorExplicit_fst
    (F := F) (Additive.ofMul f) v

theorem principalDivisorExplicit_snd_apply
    (w : NumberField.InfinitePlace F) (f : Fˣ) :
    (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)).2 w =
      archimedeanPlaceValue w f := by
  simpa using SourceModelBackendDocking.principalDivisorExplicit_snd
    (F := F) (Additive.ofMul f) w

theorem finitePlaceValueKernel_realification_eq_backendDivisor
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (finitePlaceValueKernel (F := F) v).realification
        (finitePlaceGlobalUnitValue (F := F) v f) =
      -((SourceModelBackend.coneGrothendieckEquiv (F := F)
          ((SourceModelBackend.numberFieldSourceModelInput (F := F)).divisor
            SourceModelBackend.bottomPoint (Additive.ofMul f))).1 v : ℝ) *
        Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) := by
  rw [finitePlaceValueKernel_realification_globalUnit,
    sourceModelInput_divisor_fst_eq_finiteExponent_apply,
    ← numberFieldGlobalPlaceData_finiteDelta]

theorem infinitePlaceValueKernel_realification_eq_backendDivisor
    (w : NumberField.InfinitePlace F) (f : Fˣ) :
    (infinitePlaceValueKernel (F := F) w).realification
        (Units.map (algebraMap F w.Completion).toMonoidHom f) =
      (SourceModelBackend.coneGrothendieckEquiv (F := F)
        ((SourceModelBackend.numberFieldSourceModelInput (F := F)).divisor
          SourceModelBackend.bottomPoint (Additive.ofMul f))).2 w := by
  rw [infinitePlaceValueKernel_realification_globalUnit,
    sourceModelInput_divisor_snd_eq_archimedeanValue_apply]
  simp [archimedeanPlaceValue]

theorem finitePlaceValueKernel_realification_eq_divisorRealification
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (finitePlaceValueKernel (F := F) v).realification
        (finitePlaceGlobalUnitValue (F := F) v f) =
      PrimeStripDivisorFrobenius.finiteDivisorRealification (F := F) v
        (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)) := by
  rw [finitePlaceValueKernel_realification_globalUnit]
  change -((numberFieldGlobalPlaceData (F := F)).finiteDelta f v : ℝ) *
      Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) =
    -(((SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)).1 v : ℤ) : ℝ) *
      Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ))
  rw [principalDivisorExplicit_fst_apply, numberFieldGlobalPlaceData_finiteDelta]

theorem infinitePlaceValueKernel_realification_eq_divisorRealification
    (w : NumberField.InfinitePlace F) (f : Fˣ) :
    (infinitePlaceValueKernel (F := F) w).realification
        (Units.map (algebraMap F w.Completion).toMonoidHom f) =
      PrimeStripDivisorFrobenius.archimedeanDivisorRealification (F := F) w
        (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)) := by
  rw [infinitePlaceValueKernel_realification_globalUnit]
  change (numberFieldGlobalPlaceData (F := F)).infiniteDelta f w =
    (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)).2 w
  rw [principalDivisorExplicit_snd_apply, numberFieldGlobalPlaceData_infiniteDelta]
  simp [archimedeanPlaceValue]

theorem finitePlaceValueKernel_realification_globalUnit_pow
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) (n : ℕ) :
    (finitePlaceValueKernel (F := F) v).realification
        (finitePlaceGlobalUnitValue (F := F) v (f ^ n)) =
      (n : ℝ) * (finitePlaceValueKernel (F := F) v).realification
        (finitePlaceGlobalUnitValue (F := F) v f) := by
  rw [finitePlaceValueKernel_realification_globalUnit,
    finitePlaceValueKernel_realification_globalUnit,
    GlobalPlaceData.finiteDelta_pow, nsmul_eq_mul]
  push_cast
  ring

theorem infinitePlaceValueKernel_realification_globalUnit_pow
    (w : NumberField.InfinitePlace F) (f : Fˣ) (n : ℕ) :
    (infinitePlaceValueKernel (F := F) w).realification
        (Units.map (algebraMap F w.Completion).toMonoidHom (f ^ n)) =
      (n : ℝ) * (infinitePlaceValueKernel (F := F) w).realification
        (Units.map (algebraMap F w.Completion).toMonoidHom f) := by
  rw [infinitePlaceValueKernel_realification_globalUnit,
    infinitePlaceValueKernel_realification_globalUnit,
    GlobalPlaceData.infiniteDelta_pow, nsmul_eq_mul]


def numberFieldPrimeStripComponent (P : NumberFieldPlaceIndex (F := F)) :
    PrimeStripComponent.{u} :=
  match P with
  | Sum.inl v => finitePlacePrimeStripComponent (F := F) v
  | Sum.inr w => infinitePlacePrimeStripComponent (F := F) w

noncomputable def numberFieldPrimeStrip :
    FPrimeStrip (NumberFieldPlaceIndex (F := F)) where
  Pi := fun P => (numberFieldPrimeStripComponent (F := F) P).Pi
  groupPi := fun P => (numberFieldPrimeStripComponent (F := F) P).groupPi
  G := fun P => (numberFieldPrimeStripComponent (F := F) P).G
  groupG := fun P => (numberFieldPrimeStripComponent (F := F) P).groupG
  proj := fun P => (numberFieldPrimeStripComponent (F := F) P).proj
  proj_surjective := fun P => (numberFieldPrimeStripComponent (F := F) P).proj_surjective
  Mon := fun P => (numberFieldPrimeStripComponent (F := F) P).Mon
  commMonoidMon := fun P => (numberFieldPrimeStripComponent (F := F) P).commMonoidMon
  action := fun P => (numberFieldPrimeStripComponent (F := F) P).action
  degree := fun P => (numberFieldPrimeStripComponent (F := F) P).degree

@[simp] theorem numberFieldPrimeStrip_Pi_finite
    (v : HeightOneSpectrum (𝓞 F)) :
    (numberFieldPrimeStrip (F := F)).Pi (Sum.inl v) =
      (finitePlacePrimeStripComponent (F := F) v).Pi := by
  simp [numberFieldPrimeStrip, numberFieldPrimeStripComponent]

@[simp] theorem numberFieldPrimeStrip_Mon_finite
    (v : HeightOneSpectrum (𝓞 F)) :
    (numberFieldPrimeStrip (F := F)).Mon (Sum.inl v) =
      (finitePlacePrimeStripComponent (F := F) v).Mon := by
  simp [numberFieldPrimeStrip, numberFieldPrimeStripComponent]

@[simp] theorem numberFieldPrimeStrip_Pi_infinite
    (w : NumberField.InfinitePlace F) :
    (numberFieldPrimeStrip (F := F)).Pi (Sum.inr w) =
      (infinitePlacePrimeStripComponent (F := F) w).Pi := by
  simp [numberFieldPrimeStrip, numberFieldPrimeStripComponent]

@[simp] theorem numberFieldPrimeStrip_Mon_infinite
    (w : NumberField.InfinitePlace F) :
    (numberFieldPrimeStrip (F := F)).Mon (Sum.inr w) =
      (infinitePlacePrimeStripComponent (F := F) w).Mon := by
  simp [numberFieldPrimeStrip, numberFieldPrimeStripComponent]

theorem numberFieldPrimeStrip_degree_finite
    (v : HeightOneSpectrum (𝓞 F)) :
    (numberFieldPrimeStrip (F := F)).degree (Sum.inl v) =
      finitePlaceLocalDegree (F := F) v := by
  change (finitePlacePrimeStripComponent (F := F) v).degree = _
  exact finitePlacePrimeStripComponent_degree_eq_backend (F := F) v

theorem numberFieldPrimeStrip_degree_infinite
    (w : NumberField.InfinitePlace F) :
    (numberFieldPrimeStrip (F := F)).degree (Sum.inr w) =
      infinitePlaceCompletionDegree (F := F) w := by
  change (infinitePlacePrimeStripComponent (F := F) w).degree = _
  exact infinitePlacePrimeStripComponent_degree_eq_backend (F := F) w

theorem numberFieldPrimeStrip_geometric_finite
    (v : HeightOneSpectrum (𝓞 F)) :
    (numberFieldPrimeStrip (F := F)).geometric (Sum.inl v) = ⊥ := by
  change (MonoidHom.id (AbsoluteGaloisProfinite (v.adicCompletion F))).ker = ⊥
  ext x
  simp

theorem numberFieldPrimeStrip_geometric_infinite
    (w : NumberField.InfinitePlace F) :
    (numberFieldPrimeStrip (F := F)).geometric (Sum.inr w) = ⊥ := by
  change (MonoidHom.id (AbsoluteGaloisProfinite (w.Completion))).ker = ⊥
  ext x
  simp

def finitePlacePrimeStripValueMap (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ →* Multiplicative ℤ :=
  finitePlaceLocalValue (F := F) v

theorem finitePlacePrimeStripValueMap_surjective
    (v : HeightOneSpectrum (𝓞 F)) :
    Function.Surjective (finitePlacePrimeStripValueMap (F := F) v) :=
  finitePlaceLocalValue_surjective (F := F) v

theorem finitePlacePrimeStripValueMap_ker
    (v : HeightOneSpectrum (𝓞 F)) :
    (finitePlacePrimeStripValueMap (F := F) v).ker =
      (v.adicCompletionIntegers F).units := by
  ext x
  rw [MonoidHom.mem_ker, finitePlacePrimeStripValueMap,
    finitePlaceLocalValue_eq_one_iff_mem_integralUnits]

theorem finitePlacePrimeStripComponent_Pi_eq
    (v : HeightOneSpectrum (𝓞 F)) :
    (finitePlacePrimeStripComponent (F := F) v).Pi =
      AbsoluteGaloisProfinite (v.adicCompletion F) := by
  simp [finitePlacePrimeStripComponent]

theorem infinitePlacePrimeStripComponent_Pi_eq
    (w : NumberField.InfinitePlace F) :
    (infinitePlacePrimeStripComponent (F := F) w).Pi =
      AbsoluteGaloisProfinite (w.Completion) := by
  simp [infinitePlacePrimeStripComponent]

theorem finitePlacePrimeStripComponent_Mon_eq
    (v : HeightOneSpectrum (𝓞 F)) :
    (finitePlacePrimeStripComponent (F := F) v).Mon =
      finitePlaceUnitValueMonoid (F := F) v := by
  simp [finitePlacePrimeStripComponent, finitePlaceUnitValueMonoid]

theorem numberFieldPrimeStripComponent_finite
    (v : HeightOneSpectrum (𝓞 F)) :
    numberFieldPrimeStripComponent (F := F) (Sum.inl v) =
      finitePlacePrimeStripComponent (F := F) v := by
  simp [numberFieldPrimeStripComponent]

theorem numberFieldPrimeStripComponent_infinite
    (w : NumberField.InfinitePlace F) :
    numberFieldPrimeStripComponent (F := F) (Sum.inr w) =
      infinitePlacePrimeStripComponent (F := F) w := by
  simp [numberFieldPrimeStripComponent]

theorem finitePlacePrimeStripComponent_degree_toAdd
    (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    Multiplicative.toAdd ((finitePlacePrimeStripComponent (F := F) v).degree x) =
      -((completionValuationExponent v x : ℤ) : ℝ) *
        Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) := by
  change Multiplicative.toAdd (finitePlaceCompletionDegree (F := F) v x) = _
  rw [finitePlaceCompletionDegree_apply]
  simp

theorem infinitePlacePrimeStripComponent_degree_toAdd
    (w : NumberField.InfinitePlace F) (x : (w.Completion)ˣ) :
    Multiplicative.toAdd ((infinitePlacePrimeStripComponent (F := F) w).degree x) =
      -Real.log ‖(x : w.Completion)‖ := by
  change Multiplicative.toAdd (infinitePlaceCompletionDegree (F := F) w x) = _
  rw [infinitePlaceCompletionDegree]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  rw [toAdd_ofAdd]



/-! ## Formal boundary lemma: the arithmetic component has no source geometric kernel -/

/-- At every place the projection of the constructed arithmetic number-field
prime strip is the identity, so its geometric kernel is trivial. -/
theorem numberFieldPrimeStrip_geometric_eq_bot
    (P : NumberFieldPlaceIndex (F := F)) :
    (numberFieldPrimeStrip (F := F)).geometric P = ⊥ := by
  cases P with
  | inl v => exact numberFieldPrimeStrip_geometric_finite (F := F) v
  | inr w => exact numberFieldPrimeStrip_geometric_infinite (F := F) w

/-- Formal J4 boundary lemma.  The constructed arithmetic prime strip has a
nontrivial geometric kernel nowhere, hence it is not a source-curve prime strip:
the source curve component requires a nontrivial geometric fundamental group
(HasNontrivialGeometricKernel).  The reduced anabelioid realization of
Example36EtalePiOneKernelRealization supplies such a nontrivial-kernel D-prime-strip
only as the explicit reduced model (geometric kernel model = Z/2) at rational p-adic
places, not as the actual curve fundamental group for a general number field. -/
theorem numberFieldPrimeStrip_not_hasNontrivialGeometricKernel :
    ¬ HasNontrivialGeometricKernel
      (numberFieldPrimeStrip (F := F)).toDPrimeStrip := by
  rintro ⟨P, hP⟩
  exact hP (numberFieldPrimeStrip_geometric_eq_bot (F := F) P)



/-! ## The actual Galois action on the concrete Tate layers

The arithmetic group of the affine strips below is the actual absolute Galois
group of `Q`, acting on the concrete Tate module layers of `y^2 = x^3 - x`
through the division-point Galois action of the ABC bridge. -/

open WeierstrassCurve

local instance instDecidableEqTateGeometricBasePrimeStrip : DecidableEq tateGeometricBase := Classical.decEq tateGeometricBase

/-- The actual Galois action of `Gal(Qbar/Q)` on the level-two Tate module `E[2]`
as a multiplicative automorphism. -/
noncomputable def tateLevelTwoGaloisMulAut
    (sigma : tateGeometricBase ≃ₐ[ℚ] tateGeometricBase) :
    MulAut (Multiplicative tateLevelTwoTorsion) where
  toFun x := Multiplicative.ofAdd (tateLevelTwoGaloisAction sigma x.toAdd)
  invFun x := Multiplicative.ofAdd ((tateLevelTwoGaloisAction sigma).symm x.toAdd)
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_ofAdd]
    exact map_add (tateLevelTwoGaloisAction sigma) x.toAdd y.toAdd

/-- The Galois action on `E[2]` as a monoid homomorphism into the automorphism
group of the module. -/
noncomputable def tateLevelTwoGaloisActionHom :
    (tateGeometricBase ≃ₐ[ℚ] tateGeometricBase) →*
      MulAut (Multiplicative tateLevelTwoTorsion) where
  toFun := tateLevelTwoGaloisMulAut
  map_one' := by
    ext x
    apply Multiplicative.toAdd.injective
    simp [tateLevelTwoGaloisMulAut, tateLevelTwoGaloisAction_one]
  map_mul' sigma tau := by
    ext x
    apply Multiplicative.toAdd.injective
    simp [tateLevelTwoGaloisMulAut, tateLevelTwoGaloisAction_mul]

/-- The affine D-prime-strip of the concrete level-two Tate module: the total
group is `E[2] ⋊ Gal(Qbar/Q)`, the geometric kernel is `E[2]`, and the
arithmetic group is the actual absolute Galois group of `Q`. -/
noncomputable def tateLevelTwoAffineDPrimeStrip : DPrimeStrip Unit :=
  semidirectDPrimeStrip tateLevelTwoGaloisActionHom

theorem tateLevelTwoAffineDPrimeStrip_G :
    (tateLevelTwoAffineDPrimeStrip).G () =
      (tateGeometricBase ≃ₐ[ℚ] tateGeometricBase) :=
  rfl

/-- The arithmetic group of the affine strip is the actual absolute Galois
group of `Q`. -/
theorem tateLevelTwoAffineDPrimeStrip_G_eq_absoluteGalois :
    (tateLevelTwoAffineDPrimeStrip).G () = (rationalAbsoluteGaloisGroup : Type) :=
  (rationalAbsoluteGaloisGroup_coe).symm

/-- The geometric kernel of the affine strip is multiplicatively equivalent to
the concrete level-two Tate module `E[2]`. -/
noncomputable def tateLevelTwoAffineDPrimeStrip_geometricMulEquiv :
    (tateLevelTwoAffineDPrimeStrip).geometric () ≃*
      (tateLevelTwoProfiniteGroup : Type) :=
  semidirectGeometricMulEquiv tateLevelTwoGaloisActionHom

/-- The concrete 2-torsion point `(0,0)` as an element of the geometric kernel
of the affine strip. -/
noncomputable def tateLevelTwoAffineGeometricPointZeroZero :
    (tateLevelTwoAffineDPrimeStrip).geometric () :=
  ⟨SemidirectProduct.inl (Multiplicative.ofAdd tateLevelTwoPointZeroZero), by
    change (SemidirectProduct.rightHom
      (SemidirectProduct.inl (Multiplicative.ofAdd tateLevelTwoPointZeroZero)) :
        tateGeometricBase ≃ₐ[ℚ] tateGeometricBase) = 1
    simp⟩

theorem tateLevelTwoAffineGeometricPointZeroZero_val :
    ((tateLevelTwoAffineGeometricPointZeroZero :
        (tateLevelTwoAffineDPrimeStrip).geometric ()) :
      (tateLevelTwoAffineDPrimeStrip).Pi ()) =
      SemidirectProduct.inl (Multiplicative.ofAdd tateLevelTwoPointZeroZero) :=
  rfl

theorem tateLevelTwoAffineGeometricPointZeroZero_ne_one :
    (tateLevelTwoAffineGeometricPointZeroZero :
        (tateLevelTwoAffineDPrimeStrip).Pi ()) ≠ 1 := by
  intro h
  have h2 : (SemidirectProduct.inl (Multiplicative.ofAdd tateLevelTwoPointZeroZero) :
      Multiplicative tateLevelTwoTorsion ⋊[tateLevelTwoGaloisActionHom]
        (tateGeometricBase ≃ₐ[ℚ] tateGeometricBase)) = 1 := h
  have h3 : Multiplicative.ofAdd tateLevelTwoPointZeroZero = 1 :=
    SemidirectProduct.inl_injective (by simpa using h2)
  exact tateLevelTwoPointZeroZero_ne_zero (congrArg Multiplicative.toAdd h3)

theorem tateLevelTwoAffineDPrimeStrip_geometric_ne_bot :
    (tateLevelTwoAffineDPrimeStrip).geometric () ≠ ⊥ := by
  intro hbot
  exact tateLevelTwoAffineGeometricPointZeroZero_ne_one
    (Subgroup.mem_bot.mp (hbot ▸ tateLevelTwoAffineGeometricPointZeroZero.2))

/-- The four explicit points `0, (0,0), (1,0), (-1,0)` as elements of `E[2]`. -/
noncomputable def tateLevelTwoDistinctPoints : Fin 4 → tateLevelTwoTorsion
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => tateLevelTwoPointZeroZero
  | ⟨2, _⟩ => tateLevelTwoPointOneZero
  | ⟨3, _⟩ => tateLevelTwoPointMinusOneZero
  | ⟨n + 4, hn⟩ => absurd hn (by omega)

theorem tateLevelTwoDistinctPoints_injective :
    Function.Injective tateLevelTwoDistinctPoints := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd hij.symm tateLevelTwoPointZeroZero_ne_zero
  · exact absurd hij.symm tateLevelTwoPointOneZero_ne_zero
  · exact absurd hij.symm tateLevelTwoPointMinusOneZero_ne_zero
  · exact absurd hij tateLevelTwoPointZeroZero_ne_zero
  · rfl
  · exact absurd hij tateLevelTwoPointZeroZero_ne_oneZero
  · exact absurd hij tateLevelTwoPointZeroZero_ne_minusOneZero
  · exact absurd hij tateLevelTwoPointOneZero_ne_zero
  · exact absurd hij.symm tateLevelTwoPointZeroZero_ne_oneZero
  · rfl
  · exact absurd hij tateLevelTwoPointOneZero_ne_minusOneZero
  · exact absurd hij tateLevelTwoPointMinusOneZero_ne_zero
  · exact absurd hij.symm tateLevelTwoPointZeroZero_ne_minusOneZero
  · exact absurd hij.symm tateLevelTwoPointOneZero_ne_minusOneZero
  · rfl

/-- The concrete level-two Tate module has exactly four elements. -/
theorem tateLevelTwoTorsion_card_eq_four : Nat.card tateLevelTwoTorsion = 4 := by
  rw [Nat.card_eq_fintype_card]
  have hle : Fintype.card tateLevelTwoTorsion ≤ Fintype.card (Fin 4) :=
    Fintype.card_le_of_surjective tateLevelTwoFourPoints tateLevelTwoFourPoints_surjective
  have hge : Fintype.card (Fin 4) ≤ Fintype.card tateLevelTwoTorsion :=
    Fintype.card_le_of_injective tateLevelTwoDistinctPoints
      tateLevelTwoDistinctPoints_injective
  have h := le_antisymm (by simpa using hle) (by simpa using hge)
  simpa using h

/-- The geometric kernel of the level-two affine strip has four elements. -/
theorem tateLevelTwoAffineDPrimeStrip_geometric_card :
    Nat.card ((tateLevelTwoAffineDPrimeStrip).geometric ()) = 4 := by
  refine semidirectDPrimeStrip_geometric_card tateLevelTwoGaloisActionHom ?_
  have h : Nat.card (Multiplicative tateLevelTwoTorsion) =
      Nat.card tateLevelTwoTorsion :=
    Nat.card_congr ⟨Multiplicative.toAdd, Multiplicative.ofAdd,
      fun _ => rfl, fun _ => rfl⟩
  rw [h]
  exact tateLevelTwoTorsion_card_eq_four

/-- Conjugation by the arithmetic part of the affine strip is exactly the
actual Galois action on `E[2]`: the geometric kernel is the actual Galois
module. -/
theorem tateLevelTwoAffine_conj_eq_galoisAction
    (sigma : tateGeometricBase ≃ₐ[ℚ] tateGeometricBase)
    (x : Multiplicative tateLevelTwoTorsion) :
    (SemidirectProduct.inr sigma * SemidirectProduct.inl x *
        (SemidirectProduct.inr sigma)⁻¹ :
          Multiplicative tateLevelTwoTorsion ⋊[tateLevelTwoGaloisActionHom]
            (tateGeometricBase ≃ₐ[ℚ] tateGeometricBase)) =
      SemidirectProduct.inl (tateLevelTwoGaloisActionHom sigma x) :=
  semidirectGeometric_conj tateLevelTwoGaloisActionHom sigma x

/-- The explicit orbit relation of the affine action on the level-two fiber has
a single class: the fiber is a torsor under `E[2]`, so the mono-analytic
quotient of the fiber is a point. -/
theorem tateLevelTwoAffine_fiberOrbit_subsingleton :
    Subsingleton (Quotient (semidirectAffineOrbitSetoid tateLevelTwoGaloisActionHom)) :=
  semidirectAffineOrbitSetoid_subsingleton tateLevelTwoGaloisActionHom

/-! ## The level-four affine strip -/

/-- The actual Galois action of `Gal(Qbar/Q)` on the level-four Tate module
`E[4]`. -/
noncomputable def tateLevelFourGaloisAction
    (sigma : tateGeometricBase ≃ₐ[ℚ] tateGeometricBase) :
    tateLevelFourTorsion ≃+ tateLevelFourTorsion :=
  LeanFormal.IUT.ABCBridge.Galois.galoisTorsionEquiv curveY2EqX3SubX 4 sigma

/-- The level-four Galois action as a multiplicative automorphism. -/
noncomputable def tateLevelFourGaloisMulAut
    (sigma : tateGeometricBase ≃ₐ[ℚ] tateGeometricBase) :
    MulAut (Multiplicative tateLevelFourTorsion) where
  toFun x := Multiplicative.ofAdd (tateLevelFourGaloisAction sigma x.toAdd)
  invFun x := Multiplicative.ofAdd ((tateLevelFourGaloisAction sigma).symm x.toAdd)
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_ofAdd]
    exact map_add (tateLevelFourGaloisAction sigma) x.toAdd y.toAdd

/-- The level-four Galois action as a monoid homomorphism into the automorphism
group of the module. -/
noncomputable def tateLevelFourGaloisActionHom :
    (tateGeometricBase ≃ₐ[ℚ] tateGeometricBase) →*
      MulAut (Multiplicative tateLevelFourTorsion) where
  toFun := tateLevelFourGaloisMulAut
  map_one' := by
    ext x
    apply Multiplicative.toAdd.injective
    simp [tateLevelFourGaloisMulAut, tateLevelFourGaloisAction,
      LeanFormal.IUT.ABCBridge.Galois.galoisTorsionEquiv_one_apply]
  map_mul' sigma tau := by
    ext x
    apply Multiplicative.toAdd.injective
    simp [tateLevelFourGaloisMulAut, tateLevelFourGaloisAction,
      LeanFormal.IUT.ABCBridge.Galois.galoisTorsionEquiv_mul_apply]

/-- The affine D-prime-strip of the concrete level-four Tate module. -/
noncomputable def tateLevelFourAffineDPrimeStrip : DPrimeStrip Unit :=
  semidirectDPrimeStrip tateLevelFourGaloisActionHom

/-- The geometric kernel of the level-four affine strip is multiplicatively
equivalent to the concrete `E[4]`. -/
noncomputable def tateLevelFourAffineDPrimeStrip_geometricMulEquiv :
    (tateLevelFourAffineDPrimeStrip).geometric () ≃*
      (tateLevelFourProfiniteGroup : Type) :=
  semidirectGeometricMulEquiv tateLevelFourGaloisActionHom

/-- The concrete 2-torsion point `(0,0)` inside the level-four geometric
kernel. -/
noncomputable def tateLevelFourAffineGeometricPointZeroZero :
    (tateLevelFourAffineDPrimeStrip).geometric () :=
  ⟨SemidirectProduct.inl (Multiplicative.ofAdd tateLevelFourPointZeroZero), by
    change (SemidirectProduct.rightHom
      (SemidirectProduct.inl (Multiplicative.ofAdd tateLevelFourPointZeroZero)) :
        tateGeometricBase ≃ₐ[ℚ] tateGeometricBase) = 1
    simp⟩

theorem tateLevelFourAffineGeometricPointZeroZero_val :
    ((tateLevelFourAffineGeometricPointZeroZero :
        (tateLevelFourAffineDPrimeStrip).geometric ()) :
      (tateLevelFourAffineDPrimeStrip).Pi ()) =
      SemidirectProduct.inl (Multiplicative.ofAdd tateLevelFourPointZeroZero) :=
  rfl

theorem tateLevelFourAffineGeometricPointZeroZero_ne_one :
    (tateLevelFourAffineGeometricPointZeroZero :
        (tateLevelFourAffineDPrimeStrip).Pi ()) ≠ 1 := by
  intro h
  have h2 : (SemidirectProduct.inl (Multiplicative.ofAdd tateLevelFourPointZeroZero) :
      Multiplicative tateLevelFourTorsion ⋊[tateLevelFourGaloisActionHom]
        (tateGeometricBase ≃ₐ[ℚ] tateGeometricBase)) = 1 := h
  have h3 : Multiplicative.ofAdd tateLevelFourPointZeroZero = 1 :=
    SemidirectProduct.inl_injective (by simpa using h2)
  exact tateLevelFourPointZeroZero_ne_zero (congrArg Multiplicative.toAdd h3)

theorem tateLevelFourAffineDPrimeStrip_geometric_ne_bot :
    (tateLevelFourAffineDPrimeStrip).geometric () ≠ ⊥ := by
  intro hbot
  exact tateLevelFourAffineGeometricPointZeroZero_ne_one
    (Subgroup.mem_bot.mp (hbot ▸ tateLevelFourAffineGeometricPointZeroZero.2))

/-- The level-four affine strip has a nontrivial geometric kernel. -/
theorem tateLevelFourAffineDPrimeStrip_hasNontrivialGeometricKernel :
    HasNontrivialGeometricKernel tateLevelFourAffineDPrimeStrip :=
  ⟨(), tateLevelFourAffineDPrimeStrip_geometric_ne_bot⟩

/-! ## Component identification with the divisor-side Frobenius kernels -/

/-- **Finite-place component identification.**  The component degree of the
embedded global unit, read additively, is the realification of the actual
Example 3.6 finite divisor kernel on the principal divisor. -/
theorem finitePlacePrimeStripComponent_degree_eq_finiteDivisorKernel
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    Multiplicative.toAdd ((finitePlacePrimeStripComponent (F := F) v).degree
        (finitePlaceGlobalUnitValue (F := F) v f)) =
      (PrimeStripDivisorFrobenius.finiteDivisorKernel (F := F) v).realification
        (Multiplicative.ofAdd
          (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f))) := by
  rw [PrimeStripDivisorFrobenius.finiteDivisorKernel_realification]
  exact finitePlaceValueKernel_realification_eq_divisorRealification (F := F) v f

/-- **Infinite-place component identification.**  The component degree of the
embedded global unit, read additively, is the realification of the actual
Example 3.6 archimedean divisor kernel on the principal divisor. -/
theorem infinitePlacePrimeStripComponent_degree_eq_archimedeanDivisorKernel
    (w : NumberField.InfinitePlace F) (f : Fˣ) :
    Multiplicative.toAdd ((infinitePlacePrimeStripComponent (F := F) w).degree
        (Units.map (algebraMap F w.Completion).toMonoidHom f)) =
      (PrimeStripDivisorFrobenius.archimedeanDivisorKernel (F := F) w).realification
        (Multiplicative.ofAdd
          (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f))) := by
  rw [PrimeStripDivisorFrobenius.archimedeanDivisorKernel_realification]
  exact infinitePlaceValueKernel_realification_eq_divisorRealification (F := F) w f

/-- **Finite-place Frobenius consistency.**  The component degree of the global
unit `f^n` is the realified finite divisor kernel evaluated at the degree-`n`
Frobenius action on the principal divisor of `f`: the value-side power law and
the divisor-side Frobenius action agree. -/
theorem finitePlacePrimeStripComponent_degree_pow_eq_divisorFrobenius
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) (n : ℕ) :
    Multiplicative.toAdd ((finitePlacePrimeStripComponent (F := F) v).degree
        (finitePlaceGlobalUnitValue (F := F) v (f ^ n))) =
      PrimeStripDivisorFrobenius.finiteDivisorRealification (F := F) v
        (PrimeStripDivisorFrobenius.divisorFrobenius (F := F) n
          (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f))) := by
  rw [finitePlacePrimeStripComponent_degree_eq_finiteDivisorKernel,
    PrimeStripDivisorFrobenius.finiteDivisorKernel_realification,
    ← PrimeStripDivisorFrobenius.divisorFrobenius_principalDivisorExplicit_ofMul_pow]
  simp

/-! ## The precise missing source component -/

/-- A D-prime-strip has a nontrivial geometric component at a place when its
geometric kernel there is nontrivial. -/
def HasNontrivialGeometricComponentAt {V : Type*} (D : DPrimeStrip V) (v : V) : Prop :=
  D.geometric v ≠ ⊥

/-- **The precise source requirement at a local place.**  The source local
prime strip has, at the place, an arithmetic projection with geometric kernel
multiplicatively equivalent to a prescribed nontrivial group `M` (the geometric
fundamental group).  This is a proposition, not a card: it is proved below to
imply nontriviality of the kernel, and the arithmetic number-field strip is
proved not to satisfy it because its kernel is trivial. -/
def SourceCurveGeometricComponent {V : Type*} (D : DPrimeStrip V) (v : V)
    (M : Type u) [Group M] : Prop :=
  Nontrivial M ∧ Nonempty ((D.geometric v) ≃* M)

theorem subgroup_ne_bot_of_mulEquiv_nontrivial {G : Type*} [Group G] {S : Subgroup G}
    {M : Type*} [Group M] (hM : Nontrivial M) (e : S ≃* M) : S ≠ ⊥ := by
  intro hbot
  have hsub : Subsingleton S := by
    rw [hbot]
    exact ⟨fun a b => Subtype.ext (by
      rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
  have hsubM : Subsingleton M :=
    ⟨fun a b => by
      have h := hsub.allEq (e.symm a) (e.symm b)
      simpa using congrArg e h⟩
  exact (not_nontrivial_iff_subsingleton (α := M)).mpr hsubM hM

/-- A source geometric component forces a nontrivial geometric kernel. -/
theorem hasNontrivialGeometricComponentAt_of_sourceCurve
    {V : Type*} {D : DPrimeStrip V} {v : V} {M : Type u} [Group M]
    (h : SourceCurveGeometricComponent D v M) :
    HasNontrivialGeometricComponentAt D v := by
  obtain ⟨hM, ⟨e⟩⟩ := h
  exact subgroup_ne_bot_of_mulEquiv_nontrivial hM e

/-- The concrete level-two affine strip satisfies the source geometric
component requirement with the actual level-two Tate module. -/
theorem tateLevelTwoAffine_hasNontrivialGeometricComponentAt :
    HasNontrivialGeometricComponentAt tateLevelTwoAffineDPrimeStrip () :=
  tateLevelTwoAffineDPrimeStrip_geometric_ne_bot

/-- The arithmetic number-field prime strip does not satisfy the source
geometric component requirement at any place: every local component is the
identity projection, so its geometric kernel is trivial. -/
theorem numberFieldPrimeStrip_not_hasNontrivialGeometricComponentAt
    (P : NumberFieldPlaceIndex (F := F)) :
    ¬ HasNontrivialGeometricComponentAt (numberFieldPrimeStrip (F := F)).toDPrimeStrip P := by
  intro h
  exact h (numberFieldPrimeStrip_geometric_eq_bot (F := F) P)

end LeanFormal.IUT.IUTII.Frobenioid.Example36
