/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S2570FiniteEtaleNormalActual
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# S2576: the DVR-local route to IsIntegrallyClosed Aoc2

## Context

Actual objects (all imported from S2570 / S2565 / S2566 / S2562):

* R = Z[1/Cden] = Localization (Submonoid.powers c), c = S2562.HZcMonicCActual.Cden;
* L = S1720Field, S = O_L[1/Cden], Aoc2 = Algebra.adjoin R (HZc2.rootSet L);
* Module.Finite R Aoc2, IsFractionRing Aoc2 L, and (S2570)
  IsIntegrallyClosed Aoc2 iff (forall s : S, algebraMap S L s in Aoc2).
  The only missing global input is S <= Aoc2.

The target of this file is the local-global route requested in task K3: prove the actual
DVR facts for the base, relate maximal ideals of Aoc2 to maximal ideals of R, prove
the finiteness statements that Mathlib can actually supply, and reduce

  "every maximal localization of Aoc2 is a DVR / integrally closed"

to IsIntegrallyClosed Aoc2 and to the S2570 remaining goal.  No fake closure is claimed.

## What is proved here (unconditional, no sorry / new axiom / True / native_decide)

1. R is a Dedekind domain (R_dedekind), is not a field (R_not_isField), and is
   integrally closed (R_integrallyClosed).
2. Every maximal localization R_q of R is a discrete valuation ring (rp_isDVR);
   this is IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain applied to
   the actual R = Z[1/Cden] (Dedekind, not a field, so q != bottom for maximal q).
3. For a maximal ideal p of Aoc2, the contraction q = p.comap (algebraMap R Aoc2)
   is maximal in R (overIdeal_isMaximal), using integrality of Aoc2 over R
   (Module.Finite R Aoc2 => Algebra.IsIntegral R Aoc2).
4. Module.Finite (Localization.AtPrime q)
     (Localization (algebraMapSubmonoid Aoc2 q.primeCompl))
   for every prime q (finite_localization_algebraMapSubmonoid): this is the
   unconditional finiteness of the q-localization of Aoc2 over R_q, i.e. of
   Aoc2 tensor[R] R_q in the localization presentation.
5. Module.Finite (Localization.AtPrime q) (Localization.AtPrime p) **under the
   hypothesis that q has a unique prime p of Aoc2 above it**
   (finite_atPrime_of_primesOver_eq_singleton, and its canonical form
   finite_atPrime_overIdeal).  This is exactly Mathlib's
   Localization.finite_of_primesOver_eq_singleton.
6. dvr_isIntegrallyClosed: a discrete valuation ring is integrally closed
   (from IsDiscreteValuationRing.TFAE, direction DVR <-> integrally closed with a
   unique nonzero prime).
7. The named local goals and the reductions:

   * LocalIntegrallyClosedGoal : Prop is the exact S2570 RHS
     forall p : Ideal Aoc2, p != bottom -> [p.IsMaximal] -> IsIntegrallyClosed (Aoc2_p);
   * LocalDvrGoal : Prop is the DVR form
     forall p : Ideal Aoc2, p != bottom -> [p.IsMaximal] ->
       IsDiscreteValuationRing (Aoc2_p);
   * isIntegrallyClosed_Aoc2_iff_localIntegrallyClosedGoal (S2570, restated);
   * localIntegrallyClosedGoal_of_localDvrGoal (DVR => integrally closed, pointwise);
   * isIntegrallyClosed_Aoc2_of_localDvrGoal;
   * remainingGoal_of_localDvrGoal (S2570 S <= Aoc2).

## What is *not* proved (the exact remaining inputs)

* **The local DVR/IC input itself.**  LocalDvrGoal (equivalently, by S2570,
  LocalIntegrallyClosedGoal, equivalently IsIntegrallyClosed Aoc2, equivalently
  S <= Aoc2) is not proved.  The reductions above show precisely that this local input
  would close the global gap; nothing here establishes it for the actual Aoc2.
* **Finiteness of Aoc2_p over R_q in general.**  Mathlib's available theorem needs
  q.primesOver Aoc2 = {p}; without uniqueness the AtPrime localization is a further
  localization of the finite R_q-algebra Aoc2 tensor[R] R_q and no unconditional
  Module.Finite (Localization.AtPrime q) (Localization.AtPrime p) is available from
  the imported API.  What *is* unconditional is item 4 above.
* **Regularity of Aoc2_p.**  The route "finite over a DVR + regular local of dimension
  one => DVR => integrally closed" cannot be completed here: IsDiscreteValuationRing
  is equivalent to finrank kappa (m/m^2) = 1 for a Noetherian local domain which is not
  a field (IsDiscreteValuationRing.TFAE), but Mathlib v4.32.2 has no theorem deriving
  regularity of Aoc2_p (e.g. from Algebra.Etale R Aoc2, which is still unproved,
  or from smoothness of the splitting order).  This is the same mathematical gap as
  S <= Aoc2.
* **Algebra.Etale R Aoc2** remains unproved (S2570 EtaleGoal); no theorem in
  Mathlib v4.32.2 links finite etale / smooth algebras to regularity or to
  IsIntegrallyClosed.

No sorry, no new axiom, no True/native_decide gate.
-/

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

open Polynomial
open scoped nonZeroDivisors

namespace LeanFormal.IUT.XiFPaper.S2576LocalDvrActual

open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2566AdjoinIntegralCActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
open LeanFormal.IUT.XiFPaper.S2570FiniteEtaleNormalActual

/-! ## 1. The base ring R = Z[1/Cden] -/

/-- `c = Cden` is a nonzero integer. -/
lemma hc_mem_nz : (c : ℤ) ∈ nonZeroDivisors ℤ :=
  mem_nonZeroDivisors_of_ne_zero (by simpa using hcA)

/-- `R = Z[1/Cden]` is an integral domain (localization of `Z` at a nonzero element). -/
instance instIsDomainR : IsDomain R :=
  IsLocalization.isDomain_localization (M := Submonoid.powers c)
    (Submonoid.powers_le.mpr hc_mem_nz)

/-- **`R = Z[1/Cden]` is a Dedekind domain.** -/
theorem R_dedekind : IsDedekindDomain R :=
  IsLocalization.isDedekindDomain (A := ℤ) (M := Submonoid.powers c)
    (Submonoid.powers_le.mpr hc_mem_nz) R

/-- **`R = Z[1/Cden]` is integrally closed** (localization of the integrally
closed `Z`). -/
theorem R_integrallyClosed : IsIntegrallyClosed R :=
  isIntegrallyClosed_of_isLocalization (R := ℤ) (S := R) (Submonoid.powers c)
    (Submonoid.powers_le.mpr hc_mem_nz)

/-! ### R is not a field

The prime 11 does not divide Cden (Cden = 2^34 * 3^3 * Dval, Dval = 9 mod 11),
so reduction modulo 11 gives a ring hom R ->* ZMod 11 sending 11 to 0; hence 11
is a nonzero nonunit of R. -/

/-- The auxiliary prime 11, which does not divide Cden. -/
def p11 : ℕ := 11

instance instFactP11Prime : Fact p11.Prime := ⟨by decide⟩

lemma c_mod_p11 : ((c : ℤ) : ZMod p11) ≠ 0 := by
  unfold p11 c Cden c0 Dval
  decide

/-- `c` becomes a unit in `ZMod 11`, hence the localization map
`Z -> Z[1/c]` extends to a ring homomorphism `R ->* ZMod 11`. -/
lemma isUnit_cast_p11 (y : Submonoid.powers (c : ℤ)) :
    IsUnit ((Int.castRingHom (ZMod p11)) (y : ℤ)) := by
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (y : ℤ) c).mp y.2
  rw [← hn, map_pow]
  refine IsUnit.pow n ?_
  rw [isUnit_iff_ne_zero]
  simpa using c_mod_p11

/-- The reduction `R = Z[1/Cden] -> ZMod 11` (legitimate since 11 does not divide
Cden). -/
noncomputable def toZMod : R →+* ZMod p11 :=
  IsLocalization.lift (M := Submonoid.powers c) (g := Int.castRingHom (ZMod p11))
    isUnit_cast_p11

lemma toZMod_apply (x : ℤ) : toZMod (algebraMap ℤ R x) = (x : ZMod p11) :=
  IsLocalization.lift_eq isUnit_cast_p11 x

/-- **`R = Z[1/Cden]` is not a field**: 11 is a nonzero nonunit. -/
theorem R_not_isField : ¬ IsField R := by
  intro hf
  letI := hf.toField
  have hne : algebraMap ℤ R (11 : ℤ) ≠ 0 := by
    intro h0
    have hz : (11 : ℤ) = 0 :=
      IsLocalization.injective R (M := Submonoid.powers c)
        (Submonoid.powers_le.mpr hc_mem_nz) (by simpa using h0)
    norm_num at hz
  have hunit : IsUnit (algebraMap ℤ R (11 : ℤ)) := isUnit_iff_ne_zero.mpr hne
  have hunit0 : IsUnit (toZMod (algebraMap ℤ R (11 : ℤ))) := hunit.map toZMod
  have hzero : toZMod (algebraMap ℤ R (11 : ℤ)) = 0 := by
    rw [toZMod_apply]
    decide
  rw [hzero] at hunit0
  exact not_isUnit_zero hunit0

/-! ## 2. Maximal localizations of R are discrete valuation rings -/

/-- **Every maximal localization of `R = Z[1/Cden]` is a DVR.**  R is a Dedekind
domain which is not a field, so every maximal ideal q is nonzero and
R_q = Localization.AtPrime q is a discrete valuation ring
(IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain). -/
theorem rp_isDVR (q : Ideal R) [hq : q.IsMaximal] :
    letI : q.IsPrime := hq.isPrime
    letI : IsDomain (Localization.AtPrime q) :=
      IsLocalization.isDomain_of_local_atPrime (P := q) hq.isPrime
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  haveI hq' : q.IsPrime := hq.isPrime
  haveI hdom : IsDomain (Localization.AtPrime q) :=
    IsLocalization.isDomain_of_local_atPrime (P := q) hq.isPrime
  haveI hded : IsDedekindDomain R := R_dedekind
  have hq0 : q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hq R_not_isField
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hq0 _

/-! ## 3. Maximal ideals of Aoc2 contract to maximal ideals of R -/

/-- The contraction of a prime/maximal ideal of Aoc2 to R. -/
abbrev overIdeal (p : Ideal Aoc2) : Ideal R := p.comap (algebraMap R Aoc2)

/-- **A maximal ideal of Aoc2 contracts to a maximal ideal of R.**  This uses that
Aoc2 is finite (hence integral) over R. -/
theorem overIdeal_isMaximal (p : Ideal Aoc2) [hp : p.IsMaximal] :
    (overIdeal p).IsMaximal :=
  Ideal.isMaximal_comap_of_isIntegral_of_isMaximal p

/-- The maximal ideal p of Aoc2 lies over its contraction overIdeal p. -/
theorem liesOver_overIdeal (p : Ideal Aoc2) : p.LiesOver (overIdeal p) :=
  Ideal.over_under p

/-! ## 4. Finiteness of the localizations

The unconditional statement Mathlib has is finiteness of the localization of Aoc2 at
the image of q.primeCompl over R_q (the Aoc2 tensor[R] R_q presentation).  The AtPrime
localization Aoc2_p is finite over R_q only under the additional hypothesis that q
has the single prime p of Aoc2 above it, which is exactly
Localization.finite_of_primesOver_eq_singleton. -/

/-- **Unconditional finiteness**: the q-localization of Aoc2 is finite over R_q. -/
theorem finite_localization_algebraMapSubmonoid (q : Ideal R) [hq : q.IsPrime] :
    Module.Finite (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid Aoc2 q.primeCompl)) :=
  inferInstance

/-- **Finiteness of Aoc2_p over R_q when q has a unique prime above it.**  The
algebra structure and the lying-over compatibility are hypotheses here; the canonical
instantiation is finite_atPrime_overIdeal. -/
theorem finite_atPrime_of_primesOver_eq_singleton
    (q : Ideal R) [hq : q.IsMaximal]
    (p : Ideal Aoc2) [hp : p.IsMaximal] [hpq : p.LiesOver q]
    (h : q.primesOver Aoc2 = {p})
    [Algebra (Localization.AtPrime q) (Localization.AtPrime p)]
    [Localization.AtPrime.IsLiesOverAlgebra q p] :
    Module.Finite (Localization.AtPrime q) (Localization.AtPrime p) :=
  Localization.finite_of_primesOver_eq_singleton h

/-- **Canonical form**: if the contraction q = overIdeal p of a maximal ideal p of
Aoc2 has a unique prime of Aoc2 above it (namely p), then Aoc2_p is finite over
R_q. -/
theorem finite_atPrime_overIdeal (p : Ideal Aoc2) [hp : p.IsMaximal]
    [hq : (overIdeal p).IsMaximal]
    (h : (overIdeal p).primesOver Aoc2 = {p}) :
    letI : Algebra (Localization.AtPrime (overIdeal p)) (Localization.AtPrime p) :=
      Localization.AtPrime.algebraOfLiesOver (overIdeal p) p
    Module.Finite (Localization.AtPrime (overIdeal p)) (Localization.AtPrime p) := by
  letI : Algebra (Localization.AtPrime (overIdeal p)) (Localization.AtPrime p) :=
    Localization.AtPrime.algebraOfLiesOver (overIdeal p) p
  haveI : Localization.AtPrime.IsLiesOverAlgebra (overIdeal p) p := inferInstance
  exact finite_atPrime_of_primesOver_eq_singleton (overIdeal p) p h

/-! ## 5. A DVR is integrally closed, and the local DVR reduction -/

/-- **A discrete valuation ring is integrally closed.**  This is the direction
IsDiscreteValuationRing -> IsIntegrallyClosed of IsDiscreteValuationRing.TFAE
(DVR <-> integrally closed with a unique nonzero prime). -/
theorem dvr_isIntegrallyClosed (A : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] : IsIntegrallyClosed A := by
  have h13 : IsDiscreteValuationRing A ↔
      (IsIntegrallyClosed A ∧ ∃! P : Ideal A, P ≠ ⊥ ∧ P.IsPrime) :=
    (IsDiscreteValuationRing.TFAE A (IsDiscreteValuationRing.not_isField A)).out 0 3
  exact (h13.mp inferInstance).1

/-- **The exact local integrally-closed goal** (the S2570 RHS): every maximal
localization of Aoc2 is integrally closed. -/
def LocalIntegrallyClosedGoal : Prop :=
  ∀ p : Ideal Aoc2, p ≠ ⊥ → ∀ [p.IsMaximal],
    IsIntegrallyClosed (Localization.AtPrime p)

/-- **The DVR form of the local goal**: every maximal localization of Aoc2 is a
discrete valuation ring. -/
def LocalDvrGoal : Prop :=
  ∀ p : Ideal Aoc2, p ≠ ⊥ → ∀ [p.IsMaximal],
    IsDiscreteValuationRing (Localization.AtPrime p)

/-- **IsIntegrallyClosed Aoc2 is equivalent to the local integrally-closed goal**
(this is the S2570 local-global theorem, restated as the named goal). -/
theorem isIntegrallyClosed_Aoc2_iff_localIntegrallyClosedGoal :
    IsIntegrallyClosed Aoc2 ↔ LocalIntegrallyClosedGoal :=
  isIntegrallyClosed_Aoc2_iff_localization_maximal

/-- **The local integrally-closed goal closes the global goal**: if every maximal
localization of Aoc2 is integrally closed, then Aoc2 is integrally closed. -/
theorem isIntegrallyClosed_Aoc2_of_localIntegrallyClosedGoal
    (h : LocalIntegrallyClosedGoal) : IsIntegrallyClosed Aoc2 :=
  isIntegrallyClosed_Aoc2_iff_localIntegrallyClosedGoal.mpr h

/-- **A DVR at every maximal localization makes Aoc2 locally integrally closed.** -/
theorem localIntegrallyClosedGoal_of_localDvrGoal (h : LocalDvrGoal) :
    LocalIntegrallyClosedGoal := by
  intro p hp0 hpMax
  haveI hdom : IsDomain (Localization.AtPrime p) := inferInstance
  haveI hdvr : IsDiscreteValuationRing (Localization.AtPrime p) := h p hp0
  exact dvr_isIntegrallyClosed (Localization.AtPrime p)

/-- **The DVR-local route closes the global goal**: if every maximal localization of
Aoc2 is a DVR, then Aoc2 is integrally closed. -/
theorem isIntegrallyClosed_Aoc2_of_localDvrGoal (h : LocalDvrGoal) :
    IsIntegrallyClosed Aoc2 :=
  isIntegrallyClosed_Aoc2_iff_localIntegrallyClosedGoal.mpr
    (localIntegrallyClosedGoal_of_localDvrGoal h)

/-- **Consequently the DVR-local route proves the S2570 remaining goal S <= Aoc2.** -/
theorem remainingGoal_of_localDvrGoal (h : LocalDvrGoal) :
    RemainingGoal :=
  (isIntegrallyClosed_Aoc2_iff_S_le).mp (isIntegrallyClosed_Aoc2_of_localDvrGoal h)

#print axioms R_dedekind
#print axioms R_integrallyClosed
#print axioms R_not_isField
#print axioms rp_isDVR
#print axioms overIdeal_isMaximal
#print axioms liesOver_overIdeal
#print axioms finite_localization_algebraMapSubmonoid
#print axioms finite_atPrime_of_primesOver_eq_singleton
#print axioms finite_atPrime_overIdeal
#print axioms dvr_isIntegrallyClosed
#print axioms isIntegrallyClosed_Aoc2_iff_localIntegrallyClosedGoal
#print axioms isIntegrallyClosed_Aoc2_of_localIntegrallyClosedGoal
#print axioms localIntegrallyClosedGoal_of_localDvrGoal
#print axioms isIntegrallyClosed_Aoc2_of_localDvrGoal
#print axioms remainingGoal_of_localDvrGoal

end LeanFormal.IUT.XiFPaper.S2576LocalDvrActual
end
