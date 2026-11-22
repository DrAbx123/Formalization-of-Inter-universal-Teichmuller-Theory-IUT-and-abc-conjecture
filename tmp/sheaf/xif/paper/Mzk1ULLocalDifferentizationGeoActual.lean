/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Tactic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Localization.AtPrime.Basic
import tmp.sheaf.xif.paper.Mzk1ULDifferentLocalizationActual

/-!
# Geometric localisation layer for the UL different (hbad package)

This file is the *geometric* companion of
`Mzk1ULLocalDifferentizationInterfaceActual` (arithmetic layer: `localFSum`, `rawLocalDelta`,
`localLogD`).  It provides the three localisation facts the assembling argument (david) needs in
order to pass from the global different `differentIdeal ℤ (𝓞 F)` to the per-place exponent
`delta_v` of Definition 1.9(ii).

## Proven here (unconditionally, no hypotheses)

* `absNorm_mul` : multiplicativity of `Ideal.absNorm`.  Mathlib already *has* this
  (it is `map_mul Ideal.absNorm`, because `Ideal.absNorm` is a `MonoidWithZeroHom`);
  the point of the lemma is to register the name `absNorm_mul` used by the paper assembly.
* `absNorm_mul_ringOfIntegers` : the `𝓞 F`-instance.
* `normalizedFactors_count_localized` : for a nonzero prime `P` of `𝓞 F`,
  `(normalizedFactors ((differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 F)_P))).count
      (maximalIdeal (𝓞 F)_P) = (normalizedFactors (differentIdeal ℤ (𝓞 F))).count P`.
  This is the precise `delta_v` supply for david: the exponent of the local different at `v`
  is the exponent of `P = v` in the global different.  It is a direct instantiation of
  `Mzk1ULDifferentLocalizationActual.count_normalizedFactors_map_atPrime` (DONE 23:21:30).
* `differentExponent` / `rawLocalDelta_differentExponent` : the `delta_v`-family fed into
  `rawLocalDelta` of the interface file.

## (obligation: differentIdeal_localization)

The remaining gap is the ideal-theoretic localisation identity

  `(differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (Localization.AtPrime P))
      = differentIdeal ℤ (Localization.AtPrime P)`

i.e. "the different commutes with localisation".  It is **not** in Mathlib 4.32:
`Ideal.differentIdeal` lives in `Mathlib/RingTheory/DedekindDomain/Different.lean` and what is
available there is the *tower* formula `differentIdeal_eq_differentIdeal_mul_differentIdeal`
(which needs `Module.Finite B C` and therefore cannot be applied to a localisation `S` of
`𝓞 F`, since `S` is never finite over `𝓞 F`), plus
`differentIdeal_ne_bot`, `dvd_differentIdeal_iff`, `coeIdeal_differentIdeal` and the
fractional-ideal duality `FractionalIdeal.dual`.  Nothing compares `Submodule.traceDual` for
`𝓞 F` with `Submodule.traceDual` for a localisation of `𝓞 F` (grep: `traceDual` occurs only in
`Different.lean`, `LinearDisjoint.lean`, `Trace/Basic.lean`; no localisation lemma).
This file therefore records it as an explicit obligation
`DifferentLocalizationStatement` (a `Prop`) and only *derives* its consequences
(`differentIdeal_localization`, `differentIdeal_localization_mem`).  It is never assumed
silently and there is no `sorry`.
-/

noncomputable section

open Finset
open NumberField
open IsLocalRing UniqueFactorizationMonoid
open LeanFormal.IUT.XiFPaper.Mzk1ULDifferentLocalizationActual

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace LeanFormal.IUT.XiFPaper.Mzk1ULLocalDifferentizationGeoActual

/-! ## 0. The minimal arithmetic helpers (duplicated from the interface file)

`Mzk1ULLocalDifferentizationInterfaceActual` is currently red (watchdog FAIL 2026-11-17T14:10),
so the four declarations actually needed downstream are repeated here verbatim.  Once the
interface file is green they can be replaced by the import. -/

/-- The degree denominator `sum_{v | p} f_v` of Definition 1.9(ii). -/
def localFSum {sigma : Type*} [Fintype sigma] (f : sigma → ℕ) : ℕ :=
  ∑ v, f v

/-- Raw (un-normalised) local different logarithm: `sum_{v|p} delta_v * f_v * log p`. -/
def rawLocalDelta {sigma : Type*} [Fintype sigma] (p : ℕ) (f delta : sigma → ℕ) : ℝ :=
  ∑ v, ((delta v : ℝ) * (f v : ℝ)) * Real.log (p : ℝ)

/-- The Definition 1.9(ii) local different: raw quantity divided by `sum_{v|p} f_v`. -/
def localLogD {sigma : Type*} [Fintype sigma] (p : ℕ) (f delta : sigma → ℕ) : ℝ :=
  rawLocalDelta p f delta / (localFSum f : ℝ)

/-- Multiply-back wrapper: `localLogD * localFSum = rawLocalDelta`. -/
theorem localLogD_mul_localFSum {sigma : Type*} [Fintype sigma] (p : ℕ)
    (f delta : sigma → ℕ) (h : localFSum f ≠ 0) :
    localLogD p f delta * (localFSum f : ℝ) = rawLocalDelta p f delta := by
  have h' : (localFSum f : ℝ) ≠ 0 := by exact_mod_cast h
  simp only [localLogD]
  exact div_mul_cancel₀ _ h'

/-! ## 1. Multiplicativity of the ideal norm -/

/-- **Multiplicativity of `Ideal.absNorm`.**  Registered under the name used by the paper
assembly; in Mathlib it is `map_mul` for the monoid-with-zero homomorphism `Ideal.absNorm`
(`Mathlib/RingTheory/Ideal/Norm/AbsNorm.lean`). -/
theorem absNorm_mul {S : Type*} [CommRing S] [IsDedekindDomain S] [Module.Free ℤ S]
    (I J : Ideal S) : Ideal.absNorm (I * J) = Ideal.absNorm I * Ideal.absNorm J :=
  map_mul Ideal.absNorm I J

/-- `absNorm_mul` for the ring of integers of a number field. -/
theorem absNorm_mul_ringOfIntegers {F : Type*} [Field F] [NumberField F] (I J : Ideal (𝓞 F)) :
    Ideal.absNorm (I * J) = Ideal.absNorm I * Ideal.absNorm J :=
  absNorm_mul I J

/-! ## 2. `normalizedFactors` count after localisation at a prime

The exponent `delta_v` of the different at a place `v` (with `P = v` a prime of `𝓞 F`) is the
`normalizedFactors`-count of `P` in the global different; localising does not change it, because
`(𝓞 F)_P` is unramified over the localisation of the base. -/

/-- `delta_v`: the exponent of the prime `P` in the global different `differentIdeal ℤ (𝓞 F)`. -/
noncomputable def differentExponent {F : Type*} [Field F] [NumberField F]
    (P : Ideal (𝓞 F)) : ℕ :=
  (normalizedFactors (differentIdeal ℤ (𝓞 F))).count P

/-- **Localisation of the different count.**  The exponent of the maximal ideal of `(𝓞 F)_P` in
the localised global different is the exponent of `P` in the global different, i.e. `delta_v`. -/
theorem normalizedFactors_count_localized {F : Type*} [Field F] [NumberField F]
    (P : Ideal (𝓞 F)) [P.IsPrime] (hP : P ≠ ⊥) :
    (normalizedFactors ((differentIdeal ℤ (𝓞 F)).map
        (algebraMap (𝓞 F) (Localization.AtPrime P)))).count
        (maximalIdeal (Localization.AtPrime P)) =
      (normalizedFactors (differentIdeal ℤ (𝓞 F))).count P := by
  classical
  exact count_normalizedFactors_map_atPrime P hP (differentIdeal ℤ (𝓞 F)) differentIdeal_ne_bot

/-- The `delta_v`-form of `normalizedFactors_count_localized`. -/
theorem normalizedFactors_count_localized_eq_differentExponent {F : Type*} [Field F]
    [NumberField F] (P : Ideal (𝓞 F)) [P.IsPrime] (hP : P ≠ ⊥) :
    (normalizedFactors ((differentIdeal ℤ (𝓞 F)).map
        (algebraMap (𝓞 F) (Localization.AtPrime P)))).count
        (maximalIdeal (Localization.AtPrime P)) = differentExponent P := by
  classical
  unfold differentExponent
  exact count_normalizedFactors_map_atPrime P hP (differentIdeal ℤ (𝓞 F)) differentIdeal_ne_bot

/-- `rawLocalDelta` stated directly in terms of the `delta_v` cut out by the different. -/
theorem rawLocalDelta_differentExponent {F : Type*} [Field F] [NumberField F]
    {sigma : Type*} [Fintype sigma] (p : ℕ) (f : sigma → ℕ)
    (primeOf : sigma → Ideal (𝓞 F)) :
    rawLocalDelta p f (fun v => differentExponent (primeOf v)) =
      ∑ v, (f v : ℝ) * (differentExponent (primeOf v) : ℝ) * Real.log (p : ℝ) := by
  unfold rawLocalDelta
  refine Finset.sum_congr rfl ?_
  intro v _
  ring

/-! ## 3. The localisation identity for the different ideal

`(obligation: differentIdeal_localization)`: the identity itself is *not* proved (Mathlib lacks
the localisation theory of `Submodule.traceDual`).  What is provided is the exact statement, as a
`Prop`, plus the consequences that are derived from it. -/

/-- **(obligation: differentIdeal_localization)** The exact missing statement: the different ideal
commutes with localisation at a prime of `𝓞 F`.

Mathlib 4.32 has `Ideal.differentIdeal`, `differentIdeal_eq_differentIdeal_mul_differentIdeal`
(needs `Module.Finite B C`, unusable for a localisation), `differentIdeal_ne_bot`,
`dvd_differentIdeal_iff`, `coeIdeal_differentIdeal` and `Submodule.traceDual`, but no lemma
identifying the trace dual of `𝓞 F` with that of a localisation of `𝓞 F`. -/
def DifferentLocalizationStatement {F : Type*} [Field F] [NumberField F]
    (P : Ideal (𝓞 F)) [P.IsPrime] : Prop :=
  Ideal.map (algebraMap (𝓞 F) (Localization.AtPrime P)) (differentIdeal ℤ (𝓞 F)) =
    differentIdeal ℤ (Localization.AtPrime P)

/-- **(obligation: differentIdeal_localization)** Conditional form: from the localisation identity
derive the identity.  The hypothesis is the explicit obligation above; nothing is assumed
silently. -/
theorem differentIdeal_localization {F : Type*} [Field F] [NumberField F]
    (P : Ideal (𝓞 F)) [P.IsPrime] (hbridge : DifferentLocalizationStatement P) :
    Ideal.map (algebraMap (𝓞 F) (Localization.AtPrime P)) (differentIdeal ℤ (𝓞 F)) =
      differentIdeal ℤ (Localization.AtPrime P) :=
  hbridge

/-- **(obligation: differentIdeal_localization)** The membership consequence: the image of an
element of the global different lies in the local different. -/
theorem differentIdeal_localization_mem {F : Type*} [Field F] [NumberField F]
    (P : Ideal (𝓞 F)) [P.IsPrime] (hbridge : DifferentLocalizationStatement P) {x : 𝓞 F}
    (hx : x ∈ differentIdeal ℤ (𝓞 F)) :
    algebraMap (𝓞 F) (Localization.AtPrime P) x ∈
      differentIdeal ℤ (Localization.AtPrime P) := by
  rw [← hbridge]
  exact Ideal.mem_map_of_mem (algebraMap (𝓞 F) (Localization.AtPrime P)) hx

/-- **(obligation: differentIdeal_localization)** The `≤` direction, in the form used when only
containment of the localised global different is needed. -/
theorem differentIdeal_localization_le {F : Type*} [Field F] [NumberField F]
    (P : Ideal (𝓞 F)) [P.IsPrime] (hbridge : DifferentLocalizationStatement P) :
    Ideal.map (algebraMap (𝓞 F) (Localization.AtPrime P)) (differentIdeal ℤ (𝓞 F)) ≤
      differentIdeal ℤ (Localization.AtPrime P) :=
  hbridge.le

/-- Instance-light packaging of the same obligation, for callers that cannot (or do not want to)
name `differentIdeal` at the localisation: the local different is supplied as data `J`, the
intended instantiation being `J = differentIdeal ℤ S`. -/
def DifferentLocalizationBridge (F : Type*) [Field F] [NumberField F]
    (S : Type*) [CommRing S] [Algebra (𝓞 F) S] (J : Ideal S) : Prop :=
  Ideal.map (algebraMap (𝓞 F) S) (differentIdeal ℤ (𝓞 F)) = J

/-- **(obligation: differentIdeal_localization)** Generic conditional form of the localisation
identity, with the local different as data. -/
theorem differentIdeal_localization_of_bridge (F : Type*) [Field F] [NumberField F]
    {S : Type*} [CommRing S] [Algebra (𝓞 F) S] (J : Ideal S)
    (hbridge : DifferentLocalizationBridge F S J) :
    Ideal.map (algebraMap (𝓞 F) S) (differentIdeal ℤ (𝓞 F)) = J :=
  hbridge

/-! ## Axiom audit -/

#print axioms localFSum
#print axioms rawLocalDelta
#print axioms localLogD
#print axioms localLogD_mul_localFSum
#print axioms absNorm_mul
#print axioms absNorm_mul_ringOfIntegers
#print axioms differentExponent
#print axioms normalizedFactors_count_localized
#print axioms normalizedFactors_count_localized_eq_differentExponent
#print axioms rawLocalDelta_differentExponent
#print axioms DifferentLocalizationStatement
#print axioms differentIdeal_localization
#print axioms differentIdeal_localization_mem
#print axioms differentIdeal_localization_le
#print axioms DifferentLocalizationBridge
#print axioms differentIdeal_localization_of_bridge

end LeanFormal.IUT.XiFPaper.Mzk1ULLocalDifferentizationGeoActual
