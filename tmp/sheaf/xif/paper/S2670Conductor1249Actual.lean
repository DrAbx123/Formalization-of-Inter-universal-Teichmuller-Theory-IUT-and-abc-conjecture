/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S2669Kummer1249Actual
import tmp.sheaf.xif.paper.S2582P12ClosedActual
import Mathlib.RingTheory.Conductor
import Mathlib.RingTheory.DedekindDomain.Different

/-!
# S2670: the conductor of `Z[theta]` is prime to `1249` (unconditional)

Let `F' = S1720Field`, `C = O_{F'} = S2565ConcreteIntegralClosureCActual.C`, and let
`theta = S2579Theta : C` be the explicit primitive element of S2579, with
`minpoly Z theta = S2579P12` (certificate S2582) and `F' = Q(theta)` (S2581).

This file removes the last arithmetic input `S2669Conductor1249` of the
p = 1249 Kummer--Dedekind step of S2669:

  `S2670_conductor1249 : not ((1249 : Nat) | RingOfIntegers.exponent S2579Theta)`.

Consequently `S2669_prime1249_of_conductor` is closed unconditionally: there is a
prime `P` of `S = O_{F'}[1/Cden]` over `(1249)` with residue field `ZMod 1249`
(`S2670_prime1249`).

## The conductor argument

This is a verbatim copy of the p = 613 proof of
`tmp/sheaf/xif/paper/S2584PrimeDegreeOneActual.lean`, replacing `613` by `1249`
and the twelve roots `S2580r k` modulo `613` by the twelve roots `S2669r k`
modulo `1249` (both signs of `45, 48, 124, 127, 143, 222`).

Mathlib's `conductor_mul_differentIdeal` (for the integral element `theta`) gives

  `(conductor Z theta) * differentIdeal Z C = span {aeval theta (P12')}`.

If a prime `P` above `1249` contained the conductor, then
`aeval theta P12'` would lie in `P`.  On the other hand `P12(theta) = 0`, so the
residue of `theta` in the field `C/P` would be a common root of the reductions of
`P12` and `P12'` modulo `1249`.  But S2669 factors `P12` modulo `1249` as

  `prod k : Fin 6, (X - C (r k)) * (X + C (r k))`,

a product of twelve distinct linear factors, so `P12` is separable modulo `1249`
and its reduction and that of its derivative generate the unit ideal (Bezout
identity extracted from `Polynomial.separable_def'`).  This contradiction shows
that no prime above `1249` contains the conductor, i.e.
`conductor + 1249 C = C`.

Consequently `1249` is a unit modulo the conductor.  If `1249` divided the
exponent of the conductor (equivalently, if `1249` were an element of the
conductor), then writing `exponent = 1249 * m` would force `m` into the conductor
(still modulo the conductor) while `m < exponent`, contradicting the minimality
of the exponent (`RingOfIntegers.exponent_eq_sInf`).  Hence
`S2669Conductor1249` holds.

No `sorry`, `axiom`, `True`, `native_decide` or opaque gate is used; the axiom
footprint is the usual `propext`, `Classical.choice`, `Quot.sound`.
-/

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false

open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2670Conductor1249Actual

open LeanFormal.IUT.XiFPaper.S2579Kummer613Actual
open LeanFormal.IUT.XiFPaper.S2581PrimitiveThetaActual
open LeanFormal.IUT.XiFPaper.S2582P12ClosedActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2580P12CertificateActual
open LeanFormal.IUT.XiFPaper.S2669Kummer1249Actual

local instance : Fact (Nat.Prime 1249) := ⟨by norm_num⟩

/-! ## 1. The twelve distinct roots of P12 modulo 1249 -/

/-- The twelve roots of `S2579P12` modulo `1249`: for each of the six roots
`S2669r k` of the even sextic we take both signs. -/
def S2670root : Fin 6 × Bool → ZMod 1249
  | (k, false) => S2669r k
  | (k, true) => -S2669r k

/-- The reduction of `S2579P12` modulo `1249` is the product of the twelve linear
factors attached to the distinct roots `S2670root`. -/
theorem S2670_factorization :
    S2579P12.map (Int.castRingHom (ZMod 1249)) =
      ∏ kb : Fin 6 × Bool, (X - C (S2670root kb)) := by
  rw [S2669P12_mod1249_eq, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro k _
  rw [Fintype.prod_bool]
  simp only [S2670root]
  rw [Polynomial.C_neg, sub_neg_eq_add, mul_comm]

/-- The twelve roots are pairwise distinct modulo `1249`. -/
theorem S2670_root_injective : Function.Injective S2670root := by
  rintro ⟨a, ba⟩ ⟨b, bb⟩ h
  fin_cases a <;> fin_cases b <;> cases ba <;> cases bb <;>
    simp only [S2670root, S2669r] at h ⊢
  all_goals first | rfl | (exfalso; revert h; decide)

/-- `S2579P12` is separable modulo `1249`: it is a product of distinct linear
factors. -/
theorem S2670_p12map_separable :
    (S2579P12.map (Int.castRingHom (ZMod 1249))).Separable := by
  rw [S2670_factorization]
  exact (Polynomial.separable_prod_X_sub_C_iff).mpr S2670_root_injective

/-- A Bezout identity modulo `1249` between `P12` and its derivative. -/
theorem S2670_p12map_bezout :
    ∃ a b : (ZMod 1249)[X],
      a * S2579P12.map (Int.castRingHom (ZMod 1249)) +
        b * derivative (S2579P12.map (Int.castRingHom (ZMod 1249))) = 1 :=
  (Polynomial.separable_def' _).mp S2670_p12map_separable

/-! ## 2. Primitivity and non-vanishing of the derivative at theta -/

/-- The primitivity statement of S2581, in the `Algebra.adjoin` form required by
`conductor_mul_differentIdeal`. -/
theorem S2670_hprim :
    Algebra.adjoin ℚ ({algebraMap C S1720Field S2579Theta} : Set S1720Field) = ⊤ := by
  have h := congrArg IntermediateField.toSubalgebra S2581_primitive
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (IsAlgebraic.of_finite ℚ (S2579Theta : S1720Field))] at h
  simpa using h

/-- The derivative of the minimal polynomial of `theta` does not vanish at
`theta` (separability in characteristic zero). -/
theorem S2670_haeval_ne :
    aeval S2579Theta (derivative (minpoly ℤ S2579Theta)) ≠ 0 := by
  intro h0
  have hsepQ : (minpoly ℚ (S2579Theta : S1720Field)).Separable :=
    PerfectField.separable_of_irreducible (minpoly.irreducible S2580_isIntegral_rat)
  have hderQ : aeval (S2579Theta : S1720Field)
      (derivative (minpoly ℚ (S2579Theta : S1720Field))) ≠ 0 :=
    hsepQ.aeval_derivative_ne_zero (minpoly.aeval ℚ (S2579Theta : S1720Field))
  have hmin : minpoly ℚ (S2579Theta : S1720Field) =
      (minpoly ℤ S2579Theta).map (algebraMap ℤ ℚ) := S2580_minpoly_rat
  have hder : derivative (minpoly ℚ (S2579Theta : S1720Field)) =
      (derivative (minpoly ℤ S2579Theta)).map (algebraMap ℤ ℚ) := by
    rw [hmin, Polynomial.derivative_map]
  rw [hder] at hderQ
  have hcomp : (algebraMap ℚ S1720Field).comp (algebraMap ℤ ℚ) =
      (algebraMap C S1720Field).comp (algebraMap ℤ C) := by
    ext x
    simp
  have hrel : algebraMap C S1720Field
        (aeval S2579Theta (derivative (minpoly ℤ S2579Theta))) =
      aeval (S2579Theta : S1720Field)
        ((derivative (minpoly ℤ S2579Theta)).map (algebraMap ℤ ℚ)) :=
    Polynomial.map_aeval_eq_aeval_map hcomp _ _
  apply hderQ
  rw [← hrel, h0, map_zero]

/-- The conductor of `Z[theta]` is nonzero. -/
theorem S2670_conductor_ne_bot : conductor ℤ S2579Theta ≠ ⊥ := by
  intro hbot
  have hmul := conductor_mul_differentIdeal (A := ℤ) (K := ℚ) (L := S1720Field)
    S2579Theta S2670_hprim
  have hspan : Ideal.span {aeval S2579Theta (derivative (minpoly ℤ S2579Theta))} = ⊥ := by
    rw [← hmul, hbot, Ideal.bot_mul]
  exact S2670_haeval_ne (Ideal.span_singleton_eq_bot.mp hspan)

/-- The exponent of the conductor is positive. -/
theorem S2670_exponent_pos : 0 < RingOfIntegers.exponent S2579Theta := by
  by_contra h
  have hzero : RingOfIntegers.exponent S2579Theta = 0 := Nat.eq_zero_of_not_pos h
  have hunder : Ideal.under ℤ (conductor ℤ S2579Theta) = ⊥ := by
    have habs : Ideal.absNorm (Ideal.under ℤ (conductor ℤ S2579Theta)) = 0 := by
      rw [show Ideal.absNorm (Ideal.under ℤ (conductor ℤ S2579Theta)) =
        RingOfIntegers.exponent S2579Theta from rfl, hzero]
    rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ (conductor ℤ S2579Theta)), habs]
    simp
  exact (Ideal.under_ne_bot (A := ℤ) S2670_conductor_ne_bot) hunder

/-! ## 3. No prime above 1249 contains the conductor -/

/-- If a prime `P` above `1249` contained the conductor, then the residue of
`theta` in the residue field would be a common root of `P12` and `P12'`
modulo `1249`, contradicting the Bezout identity of `S2670_p12map_bezout`. -/
theorem S2670_no_prime_over1249_le_conductor (P : Ideal C) [hPp : P.IsPrime]
    (hP : P.LiesOver (Ideal.span {(1249 : ℤ)})) :
    ¬ conductor ℤ S2579Theta ≤ P := by
  intro hle
  have hmul := conductor_mul_differentIdeal (A := ℤ) (K := ℚ) (L := S1720Field)
    S2579Theta S2670_hprim
  have hmem : aeval S2579Theta (derivative (minpoly ℤ S2579Theta)) ∈ P := by
    have hspan : Ideal.span {aeval S2579Theta (derivative (minpoly ℤ S2579Theta))} ≤ P := by
      rw [← hmul]
      exact le_trans Ideal.mul_le_right hle
    exact (Ideal.span_singleton_le_iff_mem P).mp hspan
  rw [S2582_P12Certificate] at hmem
  let t : C ⧸ P := Ideal.Quotient.mk P S2579Theta
  let psi : ZMod 1249 →+* (C ⧸ P) :=
    (algebraMap (ℤ ⧸ Ideal.span {(1249 : ℤ)}) (C ⧸ P)).comp
      (Int.quotientSpanNatEquivZMod 1249).symm.toRingHom
  letI : Algebra (ZMod 1249) (C ⧸ P) := psi.toAlgebra
  have hcompat : psi.comp (Int.castRingHom (ZMod 1249)) =
      (Ideal.Quotient.mk P).comp (algebraMap ℤ C) := by
    ext x
    change (algebraMap (ℤ ⧸ Ideal.span {(1249 : ℤ)}) (C ⧸ P))
        ((Int.quotientSpanNatEquivZMod 1249).symm (Int.castRingHom (ZMod 1249) x))
      = (Ideal.Quotient.mk P) (algebraMap ℤ C x)
    have hx : (Int.quotientSpanNatEquivZMod 1249).symm (Int.castRingHom (ZMod 1249) x)
        = Ideal.Quotient.mk (Ideal.span {(1249 : ℤ)}) x :=
      DFunLike.congr_fun (Int.quotientSpanNatEquivZMod_comp_castRingHom 1249) x
    rw [hx]
    exact Ideal.Quotient.algebraMap_mk_of_liesOver P (Ideal.span {(1249 : ℤ)}) x
  have hf0 :
      (S2579P12.map (Int.castRingHom (ZMod 1249))).eval₂ psi t = 0 := by
    rw [Polynomial.eval₂_map, hcompat]
    have h := Polynomial.hom_eval₂ S2579P12 (algebraMap ℤ C) (Ideal.Quotient.mk P) S2579Theta
    rw [← h, ← Polynomial.aeval_def, S2580_aeval_Theta]
    simp
  have hf'0 :
      (derivative (S2579P12.map (Int.castRingHom (ZMod 1249)))).eval₂ psi t = 0 := by
    rw [Polynomial.derivative_map, Polynomial.eval₂_map, hcompat]
    have h := Polynomial.hom_eval₂ (derivative S2579P12) (algebraMap ℤ C)
      (Ideal.Quotient.mk P) S2579Theta
    rw [← h, ← Polynomial.aeval_def]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  obtain ⟨a, b, hab⟩ := S2670_p12map_bezout
  have h1 := congrArg (fun p : (ZMod 1249)[X] => p.eval₂ psi t) hab
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_one,
    hf0, hf'0, mul_zero, add_zero] at h1
  exact zero_ne_one h1

/-! ## 4. The conductor is comaximal with 1249 -/

/-- No prime above `1249` contains the conductor, so the conductor and `1249 C`
generate the unit ideal. -/
theorem S2670_conductor_sup :
    conductor ℤ S2579Theta ⊔ Ideal.span {(1249 : C)} = ⊤ := by
  by_contra hne
  obtain ⟨P, hPmax, hPle⟩ := Ideal.exists_le_maximal _ hne
  haveI hPp : P.IsPrime := hPmax.isPrime
  have h1249 : (1249 : C) ∈ P :=
    hPle (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton (1249 : C))))
  have hPover : P.LiesOver (Ideal.span {(1249 : ℤ)}) := by
    refine ⟨?_.symm⟩
    have hle : Ideal.span {(1249 : ℤ)} ≤ P.under ℤ := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
      simpa using h1249
    have hne_top : P.under ℤ ≠ ⊤ := by
      intro htop
      have h1 : (1 : ℤ) ∈ P.under ℤ := by rw [htop]; exact Submodule.mem_top
      rw [Ideal.under_def, Ideal.mem_comap] at h1
      have h2 : (1 : C) ∈ P := by simpa using h1
      exact hPmax.ne_top (Ideal.eq_top_iff_one P |>.mpr h2)
    exact (Int.ideal_span_isMaximal_of_prime 1249).eq_of_le hne_top hle
  exact S2670_no_prime_over1249_le_conductor P hPover (le_trans le_sup_left hPle)

/-- `1249` does not divide the exponent of the conductor of `Z[theta]`. -/
theorem S2670_conductor1249 : S2669Conductor1249 := by
  unfold S2669Conductor1249
  intro hdiv
  obtain ⟨m, hm⟩ := hdiv
  have hunit : IsUnit (Ideal.Quotient.mk (conductor ℤ S2579Theta) (1249 : C)) := by
    have hsup := S2670_conductor_sup
    rw [Ideal.eq_top_iff_one] at hsup
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hsup
    rw [Ideal.mem_span_singleton] at hb
    obtain ⟨y, hy⟩ := hb
    have hmul1 : Ideal.Quotient.mk (conductor ℤ S2579Theta) (1249 : C) *
        Ideal.Quotient.mk (conductor ℤ S2579Theta) y = 1 := by
      rw [← map_mul, ← hy]
      have hb1 : b = 1 - a := by linear_combination hab
      rw [hb1, map_sub, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr ha, sub_zero]
    exact isUnit_iff_exists.mpr ⟨_, hmul1, by rw [mul_comm]; exact hmul1⟩
  have hmpos : 0 < m := by
    have hpos := S2670_exponent_pos
    omega
  have hmlt : m < RingOfIntegers.exponent S2579Theta := by
    rw [hm]
    nlinarith [hmpos]
  have hexp_mem : (RingOfIntegers.exponent S2579Theta : C) ∈ conductor ℤ S2579Theta :=
    Int.absNorm_under_mem (conductor ℤ S2579Theta)
  have hm_mem : (m : C) ∈ conductor ℤ S2579Theta := by
    have h0 : Ideal.Quotient.mk (conductor ℤ S2579Theta) (m : C) = 0 := by
      have hprod : Ideal.Quotient.mk (conductor ℤ S2579Theta) (m : C) *
          Ideal.Quotient.mk (conductor ℤ S2579Theta) (1249 : C) = 0 := by
        rw [← map_mul]
        have hcast : (m : C) * (1249 : C) = (RingOfIntegers.exponent S2579Theta : C) := by
          rw [hm, Nat.cast_mul]
          ring
        rw [hcast, Ideal.Quotient.eq_zero_iff_mem.mpr hexp_mem]
      exact (IsUnit.mul_left_eq_zero hunit).mp hprod
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  have hle : RingOfIntegers.exponent S2579Theta ≤ m := by
    rw [RingOfIntegers.exponent_eq_sInf]
    exact Nat.sInf_le ⟨hmpos, hm_mem⟩
  omega

/-! ## 5. The unconditional Kummer--Dedekind step at 1249 -/

/-- The linear residue factor of S2669, restated for the S2579 interface. -/
theorem S2670_linearFactor1249 : S2669LinearFactor1249 := S2669LinearFactor1249_proof

/-- The headline Kummer--Dedekind consequence of S2669, now unconditional: there
is a prime `P` of `S = O_{F'}[1/Cden]` over `(1249)` with residue field
`ZMod 1249`. -/
theorem S2670_prime1249 :
    ∃ P : Ideal S, P.IsPrime ∧ P.LiesOver (Ideal.span {(1249 : ℤ)}) ∧
      Nonempty (S ⧸ P ≃+* ZMod 1249) :=
  S2669_prime1249_of_conductor S2670_conductor1249

/-! ## 6. Axiom footprint -/

#print axioms S2670_factorization
#print axioms S2670_p12map_separable
#print axioms S2670_p12map_bezout
#print axioms S2670_hprim
#print axioms S2670_haeval_ne
#print axioms S2670_conductor_ne_bot
#print axioms S2670_exponent_pos
#print axioms S2670_no_prime_over1249_le_conductor
#print axioms S2670_conductor_sup
#print axioms S2670_conductor1249
#print axioms S2670_prime1249

end LeanFormal.IUT.XiFPaper.S2670Conductor1249Actual
