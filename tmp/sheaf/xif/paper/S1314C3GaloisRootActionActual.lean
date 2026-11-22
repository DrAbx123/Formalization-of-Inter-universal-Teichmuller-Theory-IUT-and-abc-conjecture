/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import tmp.sheaf.xif.paper.ConcreteC3RootCompletionActual
import LeanFormal.IUT.Foundations.Geometry.TateDeckAction
import LeanFormal.IUT.IUTII.Kummer.KummerClass

/-!
# S1314: the actual C3 Galois action on algebraic-closure roots

## Paper carrier

The C3 q-pilot/Kummer layer of the source is not a root system in the local
completion K_v.  In IUT II, Introduction, q_v is the q-parameter in K_v and the
source chooses a 2l-th root q~_v of q_v; the root lies in an extension of K_v,
not in K_v in general.  Kummer classes are then obtained by extracting N-th roots and
passing to Galois cohomology (IUT II, Section 3).  IUT III, Remark 3.11.4, (ii),
makes the general principle explicit: a Kummer isomorphism is determined by
(a) the cyclotome isomorphism and (b) the Galois action on the roots of the
elements of the monoid under consideration.

Consequently the root/Galois carrier is the algebraic closure

  L = AlgebraicClosure K_v

and the actual Galois action is the natural action on L^times.  In this tree the
actual action is

  NumberFieldFinitePlace.unitsAlgEquiv place : Gal(L/K_v) -> (L^times =* L^times).

It is not the completion-unit action, and the completion has no root system in
the source.  This file does not fabricate completion roots.

## What is proved

* galoisUnitsAction : Gal(L/K) ->* MulAut L^times, the actual monoid hom
  packaging unitsAlgEquiv; it fixes the algebraic-closure q-unit by
  unitsAlgEquiv_tateParameterUnit.
* galoisRootsAction : Gal(L/K) ->* Equiv.Perm (NatRootSystem qUnitAlg), the
  actual permutation action on the root systems of the fixed q-unit, with the
  root law (galoisRootsAction sigma r).root n = sigma (r.root n).
* The actual Kummer class and its root-change/root-difference identity,
  specialized to the actual action and the actual algebraic-closure roots.

## Why the literal MulAut (NatRootSystem ...) target is not used

MulAut M requires a Mul M instance.  NatRootSystem value is a root-system
torsor over the cyclotomic towers, not a group: there is no source-defined
identity or multiplication on root systems of a fixed value.  Thus the literal
type Gal(L/K) ->* MulAut (NatRootSystem value) is not well-typed.  Installing an
arbitrary group structure would be fake.  The well-typed actual rho is the pair

  rhoUnits : Gal(L/K) ->* MulAut L^times
  rhoRoots : Gal(L/K) ->* Equiv.Perm (NatRootSystem value)

with the root law recorded in ActualC3GaloisRootAction.  This is exactly the
data consumed by KummerClass.kummerClass and by the Kummer isomorphism
principle quoted above.

No sorry, admit, axiom, arbitrary data, or completion root is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1314C3GaloisRootActionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source.ConcreteC3RootTensorActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual

universe ua upi umon ui

/-! ## Root systems under a unit equivalence -/

variable {M : Type*} [CommMonoid M] {value : Mˣ}

/-- Two root systems of the same value are equal as soon as all their roots
agree.  This is the extensionality principle used for the permutation action. -/
theorem NatRootSystem.ext {r s : NatRootSystem value}
    (h : ∀ n : Nat, r.root n = s.root n) : r = s := by
  cases r with
  | mk root root_one compat =>
    cases s with
    | mk root' root_one' compat' =>
      simp only at h
      congr
      funext n
      exact h n

/-- Move a root system across a unit equivalence that fixes its value.  The
power and compatibility laws are transported through the equivalence. -/
def NatRootSystem.mapUnits (e : Mˣ ≃* Mˣ) (he : e value = value)
    (r : NatRootSystem value) : NatRootSystem value where
  root n := e (r.root n)
  root_one := by rw [r.root_one, he]
  compat n k hk := by rw [← map_pow, r.compat n k hk]

@[simp] theorem NatRootSystem.mapUnits_root
    (e : Mˣ ≃* Mˣ) (he : e value = value)
    (r : NatRootSystem value) (n : Nat) :
    (NatRootSystem.mapUnits e he r).root n = e (r.root n) := rfl

/-- The unit equivalence acts bijectively on the root systems of a fixed
value. -/
def NatRootSystem.mapUnitsEquiv (e : Mˣ ≃* Mˣ) (he : e value = value) :
    NatRootSystem value ≃ NatRootSystem value where
  toFun := NatRootSystem.mapUnits e he
  invFun := NatRootSystem.mapUnits e.symm (by
    have h := congrArg e.symm he
    simpa using h.symm)
  left_inv r := by
    apply NatRootSystem.ext
    intro n
    simp [NatRootSystem.mapUnits]
  right_inv r := by
    apply NatRootSystem.ext
    intro n
    simp [NatRootSystem.mapUnits]

@[simp] theorem NatRootSystem.mapUnitsEquiv_apply
    (e : Mˣ ≃* Mˣ) (he : e value = value)
    (r : NatRootSystem value) :
    NatRootSystem.mapUnitsEquiv e he r = NatRootSystem.mapUnits e he r := rfl

/-! ## The concrete C3 algebraic-closure carrier -/

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-- The completion at the concrete place. -/
local notation "C3K" =>
  CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place

/-- The algebraic closure of the completion: the paper's root/Galois carrier. -/
local notation "C3L" => ConcreteQAlgebraicClosure (I := I) place

/-- The actual Galois group Gal(L/K) of the algebraic closure over the
completion. -/
local notation "C3Gal" => C3L ≃ₐ[C3K] C3L

/-- The concrete q-unit in the algebraic closure is the actual Tate parameter
unit obtained by mapping the completion q-unit into L. -/
theorem concreteQUnitAlgebraicClosure_eq_tateParameterUnit :
    concreteQUnitAlgebraicClosure (I := I) place =
      tateParameterUnit place.val (concreteQCandidate I place).q
        (concreteQCandidate I place).q_ne_zero :=
  rfl

/-- The actual Galois action fixes the q-unit.  This is the fixed-unit law
needed by the Kummer construction, and it is exactly
TateDeckAction.unitsAlgEquiv_tateParameterUnit after rewriting the concrete
q-unit as the Tate parameter unit. -/
theorem galoisUnits_fixed (σ : C3Gal) :
    unitsAlgEquiv place.val σ
        (concreteQUnitAlgebraicClosure (I := I) place) =
      concreteQUnitAlgebraicClosure (I := I) place := by
  rw [concreteQUnitAlgebraicClosure_eq_tateParameterUnit]
  exact unitsAlgEquiv_tateParameterUnit place.val
    (concreteQCandidate I place).q (concreteQCandidate I place).q_ne_zero σ

/-- The actual Galois action on the carrier units L^times.  This is the rho that
KummerClass.kummerClass consumes. -/
noncomputable def galoisUnitsAction : C3Gal →* MulAut ((C3L)ˣ) where
  toFun σ := unitsAlgEquiv place.val σ
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Units.ext
    rfl
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro x
    apply Units.ext
    rfl

@[simp] theorem galoisUnitsAction_apply (σ : C3Gal) :
    galoisUnitsAction I place σ = unitsAlgEquiv place.val σ := rfl

/-- The packaged action fixes the q-unit. -/
theorem galoisUnitsAction_fixed (σ : C3Gal) :
    galoisUnitsAction I place σ
        (concreteQUnitAlgebraicClosure (I := I) place) =
      concreteQUnitAlgebraicClosure (I := I) place :=
  galoisUnits_fixed I place σ

/-- The actual permutation action on the algebraic-closure root systems of the
fixed q-unit. -/
noncomputable def galoisRootsAction :
    C3Gal →* Equiv.Perm
      (NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place)) where
  toFun σ := NatRootSystem.mapUnitsEquiv (unitsAlgEquiv place.val σ)
    (galoisUnits_fixed I place σ)
  map_one' := by
    apply Equiv.ext
    intro r
    apply NatRootSystem.ext
    intro n
    rfl
  map_mul' σ τ := by
    apply Equiv.ext
    intro r
    apply NatRootSystem.ext
    intro n
    rfl

/-- Root law: the action on roots is the action on the ambient unit carrier. -/
@[simp] theorem galoisRootsAction_root (σ : C3Gal)
    (r : NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place))
    (n : Nat) :
    (galoisRootsAction I place σ r).root n =
      unitsAlgEquiv place.val σ (r.root n) := rfl

/-- The root law in terms of the packaged unit action. -/
theorem galoisRootsAction_root_eq_unitsAction (σ : C3Gal)
    (r : NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place))
    (n : Nat) :
    (galoisRootsAction I place σ r).root n =
      galoisUnitsAction I place σ (r.root n) := rfl

theorem galoisRootsAction_one
    (r : NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place)) :
    galoisRootsAction I place 1 r = r := by
  rw [MonoidHom.map_one]
  rfl

theorem galoisRootsAction_mul (σ τ : C3Gal)
    (r : NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place)) :
    galoisRootsAction I place (σ * τ) r =
      galoisRootsAction I place σ (galoisRootsAction I place τ r) := by
  rw [MonoidHom.map_mul, Equiv.Perm.mul_apply]

/-- The acted-on root system is again a root system of the same fixed q-unit. -/
theorem galoisRootsAction_pow_self (σ : C3Gal)
    (r : NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place))
    (n : Nat) (hn : n ≠ 0) :
    (galoisRootsAction I place σ r).root n ^ n =
      concreteQUnitAlgebraicClosure (I := I) place :=
  NatRootSystem.pow_self (galoisRootsAction I place σ r) n hn

theorem galoisRootsAction_root_one (σ : C3Gal)
    (r : NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place)) :
    (galoisRootsAction I place σ r).root 1 =
      concreteQUnitAlgebraicClosure (I := I) place :=
  (galoisRootsAction I place σ r).root_one

theorem galoisRootsAction_root_compat (σ : C3Gal)
    (r : NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place))
    (n k : Nat) (hk : k ≠ 0) :
    (galoisRootsAction I place σ r).root (n * k) ^ k =
      (galoisRootsAction I place σ r).root n :=
  (galoisRootsAction I place σ r).compat n k hk

/-- The actual C3 package: unit action, root permutation action, the root law,
and the fixed q-unit law.  This is the well-typed replacement for the literal
(ill-typed) Gal(L/K) ->* MulAut (NatRootSystem ...) target. -/
structure ActualC3GaloisRootAction where
  rhoUnits : C3Gal →* MulAut ((C3L)ˣ)
  rhoRoots : C3Gal →* Equiv.Perm
    (NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place))
  root_law : ∀ (σ : C3Gal)
      (r : NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place))
      (n : Nat),
    (rhoRoots σ r).root n = rhoUnits σ (r.root n)
  fixed_q : ∀ σ : C3Gal,
    rhoUnits σ (concreteQUnitAlgebraicClosure (I := I) place) =
      concreteQUnitAlgebraicClosure (I := I) place

/-- The actual C3 Galois root action built from the algebraic closure. -/
noncomputable def actualC3GaloisRootAction : ActualC3GaloisRootAction I place where
  rhoUnits := galoisUnitsAction I place
  rhoRoots := galoisRootsAction I place
  root_law := by
    intro σ r n
    rfl
  fixed_q := galoisUnitsAction_fixed I place

@[simp] theorem actualC3GaloisRootAction_rhoUnits :
    (actualC3GaloisRootAction I place).rhoUnits = galoisUnitsAction I place := rfl

@[simp] theorem actualC3GaloisRootAction_rhoRoots :
    (actualC3GaloisRootAction I place).rhoRoots = galoisRootsAction I place := rfl

/-! ## The actual Kummer class and root change -/

/-- The actual Kummer class at a Galois element, formed from the actual action
and the actual algebraic-closure root system. -/
noncomputable def actualC3KummerClass (σ : C3Gal) : CyclotomicTower C3L :=
  KummerClass.kummerClass (galoisUnitsAction I place)
    (concreteRootsAlgebraicClosure (I := I) place)
    (galoisUnitsAction_fixed I place) σ

/-- Component formula of the actual Kummer class. -/
theorem actualC3KummerClass_component (σ : C3Gal) (n : Nat) :
    (actualC3KummerClass I place σ).component n =
      galoisUnitsAction I place σ
          ((concreteRootsAlgebraicClosure (I := I) place).root n) /
        (concreteRootsAlgebraicClosure (I := I) place).root n := rfl

/-- The Kummer class is the root-system difference between the chosen roots and
their Galois twist.  This is the root-law form of the class. -/
theorem actualC3KummerClass_eq_rootSystemDiff (σ : C3Gal) :
    actualC3KummerClass I place σ =
      KummerClass.rootSystemDiff
        (concreteRootsAlgebraicClosure (I := I) place)
        (galoisRootsAction I place σ
          (concreteRootsAlgebraicClosure (I := I) place)) := by
  apply CyclotomicTower.ext
  intro n
  rfl

/-- The class at the identity is the trivial tower. -/
theorem actualC3KummerClass_one :
    actualC3KummerClass I place 1 = CyclotomicTower.one :=
  KummerClass.kummerClass_one (galoisUnitsAction I place)
    (concreteRootsAlgebraicClosure (I := I) place)
    (galoisUnitsAction_fixed I place)

/-- The crossed multiplication law of the actual Kummer class. -/
theorem actualC3KummerClass_mul (σ τ : C3Gal) :
    actualC3KummerClass I place (σ * τ) =
      CyclotomicTower.mul
        (KummerClass.action (galoisUnitsAction I place) σ
          (actualC3KummerClass I place τ))
        (actualC3KummerClass I place σ) :=
  KummerClass.kummerClass_mul (galoisUnitsAction I place)
    (concreteRootsAlgebraicClosure (I := I) place)
    (galoisUnitsAction_fixed I place) σ τ

/-- The actual root change between the chosen roots and the Galois-twisted
roots, as the Kummer root-system difference. -/
noncomputable def actualC3RootChange (σ : C3Gal) : CyclotomicTower C3L :=
  KummerClass.rootSystemDiff
    (concreteRootsAlgebraicClosure (I := I) place)
    (galoisRootsAction I place σ
      (concreteRootsAlgebraicClosure (I := I) place))

/-- The actual root change is exactly the root-system difference (definitional
form, kept as a theorem for consumers). -/
theorem actualC3RootChange_eq (σ : C3Gal) :
    actualC3RootChange I place σ =
      KummerClass.rootSystemDiff
        (concreteRootsAlgebraicClosure (I := I) place)
        (galoisRootsAction I place σ
          (concreteRootsAlgebraicClosure (I := I) place)) := rfl

/-- The actual Kummer class is the actual root change. -/
theorem actualC3KummerClass_eq_rootChange (σ : C3Gal) :
    actualC3KummerClass I place σ = actualC3RootChange I place σ :=
  actualC3KummerClass_eq_rootSystemDiff I place σ

/-- Change-of-roots coboundary identity, specialized to the actual action and
root system. -/
theorem actualC3KummerClass_diff (σ : C3Gal)
    (first second : NatRootSystem
      (concreteQUnitAlgebraicClosure (I := I) place)) :
    CyclotomicTower.mul
        (KummerClass.kummerClass (galoisUnitsAction I place) second
          (galoisUnitsAction_fixed I place) σ)
        (KummerClass.rootSystemDiff first second) =
      CyclotomicTower.mul
        (KummerClass.kummerClass (galoisUnitsAction I place) first
          (galoisUnitsAction_fixed I place) σ)
        (KummerClass.action (galoisUnitsAction I place) σ
          (KummerClass.rootSystemDiff first second)) :=
  KummerClass.kummerClass_diff (galoisUnitsAction I place)
    (galoisUnitsAction_fixed I place) first second σ

/-- Root-motion criterion: if a Galois element moves one chosen root, then
the permutation action on the root system is nontrivial. -/
theorem galoisRootsAction_ne_one_of_root_ne (σ : C3Gal)
    (r : NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place))
    (n : Nat)
    (h : unitsAlgEquiv place.val σ (r.root n) ≠ r.root n) :
    galoisRootsAction I place σ r ≠ r := by
  intro hfix
  have hroot : (galoisRootsAction I place σ r).root n = r.root n := by
    rw [hfix]
  rw [galoisRootsAction_root] at hroot
  exact h hroot

/-- Nontriviality criterion for the actual Kummer class: a moved chosen root
produces a nontrivial component of the actual class.  This is the exact
root-law consequence; producing an actual moving Galois element remains a
separate source datum. -/
theorem actualC3KummerClass_component_ne_one_of_root_ne (σ : C3Gal)
    (n : Nat)
    (h : unitsAlgEquiv place.val σ
        ((concreteRootsAlgebraicClosure (I := I) place).root n) ≠
      (concreteRootsAlgebraicClosure (I := I) place).root n) :
    (actualC3KummerClass I place σ).component n ≠ 1 := by
  intro hcomp
  apply h
  have h' : galoisUnitsAction I place σ
      ((concreteRootsAlgebraicClosure (I := I) place).root n) /
        (concreteRootsAlgebraicClosure (I := I) place).root n = 1 := by
    simpa [actualC3KummerClass_component] using hcomp
  exact div_eq_one.mp h'

end LeanFormal.IUT.XiFPaper.S1314C3GaloisRootActionActual

end