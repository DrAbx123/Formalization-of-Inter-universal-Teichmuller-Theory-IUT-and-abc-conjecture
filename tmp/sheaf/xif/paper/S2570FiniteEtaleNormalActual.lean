/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S2567IsFractionRingAdjoinCActual
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# S2570: finite étale algebras over normal domains, and the `Aoc2` reduction

## What Mathlib has (v4.32.2)

* `IsIntegrallyClosed R` is defined as `IsIntegrallyClosedIn R (FractionRing R)`
  (`Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean`).  Mathlib has no
  separate `NormalDomain` class; the file's TODO says that the results collected
  around `IsIntegrallyClosed` are the normal-domain API.
* `Algebra.Etale R A` is `FormallyEtale R A ∧ FinitePresentation R A`
  (`Mathlib/RingTheory/Etale/Basic.lean`).  `Algebra.FormallyEtale` is the
  infinitesimal lifting property, `FormallyUnramified ∧ FormallySmooth`.
* `Mathlib/RingTheory/LocalRing/Etale.lean` proves that a finite étale extension
  of local rings is monogenic and that the derivative of the minimal polynomial
  at a generator is a unit.  It does **not** prove that a finite étale algebra
  over a normal/integrally closed domain is integrally closed.
* A grep of `Mathlib` finds no theorem relating `Algebra.Etale`,
  `FormallyEtale` or `FormallyUnramified` to `IsIntegrallyClosed`, and no
  discriminant criterion for étale/unramified algebras.  In particular the
  implication "finite étale over a normal domain is normal" is **not** available.

## The literal generic statement is vacuous

`finiteEtale_normal_isIntegrallyClosed` below is the statement requested in the
task, with both `[IsFractionRing R K]` and `[IsFractionRing A K]`.  It is true,
but its two fraction-ring hypotheses force `K = Frac R = Frac A`, and then
`Module.Finite R A` makes `A` an integral `R`-subalgebra of `K`.  Since `R` is
integrally closed in `K`, the map `R → A` is bijective: `A = R`.  The proof
below even constructs the ring equivalence.  Consequently the étale hypothesis
is unused and the theorem cannot be applied to `Aoc2`:
in the concrete situation `R = ℤ[1/Cden]` has fraction field `ℚ`, while
`L = S1720Field` is a number field containing a root of `X^2 + 1`, so
`IsFractionRing R L` is false.  The intended hypothesis can therefore only be
`[IsFractionRing Aoc2 L]` (S2567), not `[IsFractionRing R L]`.

## What is proved here

* `isIntegrallyClosed_of_isIntegralClosure`: a genuinely useful generic
  reduction.  If `A` is integral over `R` and is the integral closure of `R` in
  a fraction field `K` of `A`, then `A` is integrally closed.
* `Module.Finite R Aoc2` (instance), `Algebra.IsIntegral R Aoc2`,
  `Algebra.FiniteType R Aoc2`, `IsDomain Aoc2`.
* `instIsFractionRingAoc2`: the S2567 theorem `IsFractionRing Aoc2 L`,
  registered as an instance (its `.olean` was built after the S2566 chain).
* `isIntegrallyClosed_Aoc2_iff_isIntegralClosure` and
  `isIntegrallyClosed_Aoc2_iff_S_le`, plus the unconditional versions
  `..._unconditional`:

    `IsIntegrallyClosed Aoc2 ↔ IsIntegralClosure Aoc2 R L ↔ ∀ s : S, algebraMap S L s ∈ Aoc2`.

  Since `Aoc2 ≤ S` is known (S2566) and `S` is the integral closure of `R` in
  `L` (S2565), the remaining mathematical input is exactly `S ≤ Aoc2`
  (equivalently `Aoc2 = S`).
* `isIntegrallyClosed_Aoc2_iff_localization_maximal`: the local-global
  reduction via `IsIntegrallyClosed.of_localization_maximal`.
* `EtaleGoal` records `Algebra.Etale R Aoc2`; it is **not** proved.  Mathlib has
  no theorem deriving formal étaleness from a unit discriminant, and deriving it
  here would require formalizing the unit-discriminant/unramified criterion for
  the splitting order.  The reduction above deliberately bypasses it.

No `sorry`, no new axiom, no `True`/`native_decide` gate.
-/

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2570FiniteEtaleNormalActual

open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2566AdjoinIntegralCActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
open LeanFormal.IUT.XiFPaper.S2567IsFractionRingAdjoinCActual

/-- The S2567 theorem, registered as the fraction-ring instance for `Aoc2`. -/
instance instIsFractionRingAoc2 : IsFractionRing Aoc2 L := S2567_isFractionRing

/-! ## 1. The generic statements -/

/-- **Literal version of the requested theorem.**  The hypotheses
`[IsFractionRing R K]` and `[IsFractionRing A K]` together with
`[Module.Finite R A]` force `A = R`, so this is true but does not apply to
`Aoc2` (where `IsFractionRing R L` fails).  See the module docstring. -/
theorem finiteEtale_normal_isIntegrallyClosed
    {R A K : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing A] [IsDomain A] [Algebra R A] [Module.Finite R A]
    [Field K] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
    [IsFractionRing R K] [IsFractionRing A K]
    (het : Algebra.Etale R A) : IsIntegrallyClosed A := by
  haveI : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  -- `R → A` is injective because `R → K` is.
  have hinj : Function.Injective (algebraMap R A) := by
    intro x y h
    apply IsFractionRing.injective R K
    simpa only [← IsScalarTower.algebraMap_apply R A K] using congrArg (algebraMap A K) h
  -- `R → A` is surjective because an element of `A` is integral over `R`,
  -- and `R` is integrally closed in `K`.
  have hsurj : Function.Surjective (algebraMap R A) := by
    intro a
    have hx : IsIntegral A (algebraMap A K a) := isIntegral_algebraMap
    have hxR : IsIntegral R (algebraMap A K a) :=
      isIntegral_trans (R := R) (A := A) _ hx
    obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff (R := R) (K := K)).mp hxR
    refine ⟨r, ?_⟩
    apply IsFractionRing.injective A K
    simpa only [← IsScalarTower.algebraMap_apply R A K] using hr
  exact IsIntegrallyClosed.of_equiv (RingEquiv.ofBijective (algebraMap R A) ⟨hinj, hsurj⟩)

/-- **The provable generic reduction.**  If `A` is integral over `R` and is the
integral closure of `R` in a fraction field `K` of `A`, then `A` is integrally
closed.  This is the form in which the finite étale/normal input would be used:
for `Aoc2` it reduces `IsIntegrallyClosed Aoc2` to
`IsIntegralClosure Aoc2 R L`. -/
theorem isIntegrallyClosed_of_isIntegralClosure
    {R A K : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Field K] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
    [IsDomain A] [IsFractionRing A K] [Algebra.IsIntegral R A]
    (h : IsIntegralClosure A R K) : IsIntegrallyClosed A := by
  rw [isIntegrallyClosed_iff (K := K)]
  intro x hx
  exact IsIntegralClosure.isIntegral_iff.mp (isIntegral_trans (R := R) (A := A) x hx)

/-! ## 2. Concrete facts about `Aoc2` -/

/-- `Aoc2` is a domain: it is a subalgebra of the field `L`. -/
theorem isDomain_Aoc2 : IsDomain Aoc2 := inferInstance

/-- `Aoc2` is generated by the finite root set of `HZc2`, whose elements are
integral over `R`.  Hence it is a finite `R`-module. -/
instance instModuleFinite : Module.Finite R Aoc2 := by
  letI : Algebra R2 L := inferInstanceAs (Algebra R L)
  exact Algebra.finite_adjoin_of_finite_of_isIntegral (R := R) (A := L)
    (s := HZc2.rootSet L) (Polynomial.rootSet_finite HZc2 L)
    (fun x hx => HZc2_root_isIntegral hx)

/-- `Aoc2` is integral over `R`. -/
theorem algebraIsIntegral_Aoc2 : Algebra.IsIntegral R Aoc2 := inferInstance

/-- `Aoc2` is finitely generated as an `R`-algebra. -/
theorem finiteType_Aoc2 : Algebra.FiniteType R Aoc2 := by
  letI : Algebra R2 L := inferInstanceAs (Algebra R L)
  exact Algebra.FiniteType.adjoin_of_finite (R := R) (A := L)
    (t := HZc2.rootSet L) (Polynomial.rootSet_finite HZc2 L)

/-! ## 3. The reduction `IsIntegrallyClosed Aoc2 ↔ S ≤ Aoc2`

The S2567 result `IsFractionRing Aoc2 L` is registered as the instance
`instIsFractionRingAoc2` above.  The theorems below keep the instance argument
explicit for robustness; the `..._unconditional` corollaries at the end of this
section use the registered instance. -/

/-- If every element of `S` (the integral closure of `R` in `L`) lies in
`Aoc2`, then `Aoc2` is the integral closure of `R` in `L`. -/
theorem isIntegralClosure_Aoc2_of_S_le
    [IsFractionRing Aoc2 L] (h : ∀ s : S, algebraMap S L s ∈ Aoc2) :
    IsIntegralClosure Aoc2 R L := by
  refine ⟨IsFractionRing.injective Aoc2 L, ?_⟩
  intro x
  constructor
  · intro hx
    haveI : IsIntegralClosure S R L := S2555_isIntegralClosure
    obtain ⟨s, hs⟩ := (IsIntegralClosure.isIntegral_iff (R := R) (A := S) (B := L)).mp hx
    exact ⟨⟨algebraMap S L s, h s⟩, hs⟩
  · rintro ⟨a, rfl⟩
    exact adjoin2_root_integral a.2

/-- Conversely, if `Aoc2` is integrally closed in `L`, then it contains the
integral closure `S` of `R` in `L`.  This is the S2568 argument, reproduced
here so that the equivalence is self-contained. -/
theorem S_le_Aoc2_of_isIntegrallyClosed
    [IsFractionRing Aoc2 L] (h : IsIntegrallyClosed Aoc2) :
    ∀ s : S, algebraMap S L s ∈ Aoc2 := by
  intro s
  haveI : IsIntegralClosure S R L := S2555_isIntegralClosure
  have hxR : IsIntegral R (algebraMap S L s) :=
    IsIntegral.map (IsScalarTower.toAlgHom R S L)
      (IsIntegralClosure.isIntegral (R := R) (A := S) (B := L) s)
  have hxA : IsIntegral Aoc2 (algebraMap S L s) := hxR.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Aoc2) (K := L)).mp hxA
  rw [← hy]
  exact y.2

/-- `Aoc2` is the integral closure of `R` in `L` iff it contains `S`. -/
theorem isIntegralClosure_Aoc2_iff_S_le [IsFractionRing Aoc2 L] :
    IsIntegralClosure Aoc2 R L ↔ ∀ s : S, algebraMap S L s ∈ Aoc2 := by
  constructor
  · intro hcl s
    haveI : IsIntegralClosure S R L := S2555_isIntegralClosure
    have hs : IsIntegral R (algebraMap S L s) :=
      IsIntegral.map (IsScalarTower.toAlgHom R S L)
        (IsIntegralClosure.isIntegral (R := R) (A := S) (B := L) s)
    obtain ⟨a, ha⟩ := (IsIntegralClosure.isIntegral_iff (R := R) (A := Aoc2) (B := L)).mp hs
    rw [← ha]
    exact a.2
  · exact isIntegralClosure_Aoc2_of_S_le

/-- `Aoc2` is integrally closed iff it is the integral closure of `R` in `L`. -/
theorem isIntegrallyClosed_Aoc2_iff_isIntegralClosure [IsFractionRing Aoc2 L] :
    IsIntegrallyClosed Aoc2 ↔ IsIntegralClosure Aoc2 R L := by
  constructor
  · intro h
    haveI : IsIntegrallyClosedIn Aoc2 L :=
      (isIntegrallyClosed_iff_isIntegrallyClosedIn (R := Aoc2) L).mp h
    exact IsIntegralClosure.of_isIntegrallyClosedIn
  · intro hcl
    exact isIntegrallyClosed_of_isIntegralClosure (R := R) (K := L) hcl

/-- **The exact remaining mathematical statement**, in the form needed by the
current chain: `Aoc2` is integrally closed iff the localized ring of integers
`S` is contained in `Aoc2` (equivalently `Aoc2 = S`). -/
theorem isIntegrallyClosed_Aoc2_iff_S_le [IsFractionRing Aoc2 L] :
    IsIntegrallyClosed Aoc2 ↔ ∀ s : S, algebraMap S L s ∈ Aoc2 :=
  (isIntegrallyClosed_Aoc2_iff_isIntegralClosure).trans isIntegralClosure_Aoc2_iff_S_le

/-- The remaining goal, as a named proposition. -/
def RemainingGoal : Prop := ∀ s : S, algebraMap S L s ∈ Aoc2

/-- The remaining goal (integral-closure form). -/
def RemainingGoalIntegralClosure : Prop := IsIntegralClosure Aoc2 R L

/-- `Algebra.Etale R Aoc2` is **not** proved in this file; see the module
docstring.  It is recorded as a named proposition so that a future proof can
target exactly this statement. -/
def EtaleGoal : Prop := Algebra.Etale R Aoc2

/-- The reduction interface: if the remaining goal holds, then `Aoc2` is
integrally closed. -/
theorem isIntegrallyClosed_Aoc2_of_remaining [IsFractionRing Aoc2 L]
    (h : RemainingGoal) : IsIntegrallyClosed Aoc2 :=
  isIntegrallyClosed_Aoc2_iff_S_le.mpr h

/-- **Unconditional form** (using the S2567 instance): `Aoc2` is integrally
closed iff `S ≤ Aoc2`. -/
theorem isIntegrallyClosed_Aoc2_iff_S_le_unconditional :
    IsIntegrallyClosed Aoc2 ↔ ∀ s : S, algebraMap S L s ∈ Aoc2 :=
  isIntegrallyClosed_Aoc2_iff_S_le

/-- **Unconditional form**: `Aoc2` is integrally closed iff it is the integral
closure of `R` in `L`. -/
theorem isIntegrallyClosed_Aoc2_iff_isIntegralClosure_unconditional :
    IsIntegrallyClosed Aoc2 ↔ IsIntegralClosure Aoc2 R L :=
  isIntegrallyClosed_Aoc2_iff_isIntegralClosure

/-- **Unconditional form** of the reduction interface. -/
theorem isIntegrallyClosed_Aoc2_of_remaining_unconditional
    (h : RemainingGoal) : IsIntegrallyClosed Aoc2 :=
  isIntegrallyClosed_Aoc2_of_remaining h

/-! ## 4. The local-global reduction -/

/-- `IsIntegrallyClosed` is local at maximal ideals
(`IsIntegrallyClosed.of_localization_maximal`): it suffices to prove that every
maximal localization of `Aoc2` is integrally closed.  The forward direction uses
that a localization of an integrally closed domain is integrally closed. -/
theorem isIntegrallyClosed_Aoc2_iff_localization_maximal :
    IsIntegrallyClosed Aoc2 ↔
      ∀ p : Ideal Aoc2, p ≠ ⊥ → ∀ [p.IsMaximal],
        IsIntegrallyClosed (Localization.AtPrime p) := by
  constructor
  · intro h p _ _
    exact isIntegrallyClosed_of_isLocalization (S := Localization.AtPrime p)
      (M := p.primeCompl)
      (fun x hx => mem_nonZeroDivisors_iff_ne_zero.mpr
        (fun h0 => hx (h0 ▸ p.zero_mem)))
  · intro h
    exact IsIntegrallyClosed.of_localization_maximal h

#print axioms finiteEtale_normal_isIntegrallyClosed
#print axioms isIntegrallyClosed_of_isIntegralClosure
#print axioms instModuleFinite
#print axioms finiteType_Aoc2
#print axioms isIntegralClosure_Aoc2_of_S_le
#print axioms S_le_Aoc2_of_isIntegrallyClosed
#print axioms isIntegralClosure_Aoc2_iff_S_le
#print axioms isIntegrallyClosed_Aoc2_iff_isIntegralClosure
#print axioms isIntegrallyClosed_Aoc2_iff_S_le
#print axioms isIntegrallyClosed_Aoc2_of_remaining
#print axioms isIntegrallyClosed_Aoc2_iff_S_le_unconditional
#print axioms isIntegrallyClosed_Aoc2_iff_isIntegralClosure_unconditional
#print axioms isIntegrallyClosed_Aoc2_of_remaining_unconditional
#print axioms isIntegrallyClosed_Aoc2_iff_localization_maximal

end LeanFormal.IUT.XiFPaper.S2570FiniteEtaleNormalActual
end
