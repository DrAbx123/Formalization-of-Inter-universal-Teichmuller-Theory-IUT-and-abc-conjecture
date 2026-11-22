import tmp.sheaf.xif.paper.S2582P12ClosedActual
import tmp.sheaf.xif.paper.S2581PrimitiveThetaActual
import tmp.sheaf.xif.paper.S2579Kummer613Actual
import Mathlib.RingTheory.Conductor
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.RingTheory.DedekindDomain.Different

/-!
# S2584: the degree-one prime over 613 of F' (unconditional)

Let `F' = S1720Field`, `C = O_{F'} = S2565ConcreteIntegralClosureCActual.C`,
`S = O_{F'}[1/Cden]`, and let
`theta = S2579Theta : C` be the explicit primitive element of S2579, with
`minpoly Z theta = S2579P12` (certificate S2582).

This file removes the last arithmetic input `S2579Conductor613` of S2579 and hence
constructs an actual prime ideal `p` of `C` above `613` with residue field
`ZMod 613`, together with the extended prime `P = p.map (algebraMap C S)` of `S`
and the residue equivalences `C/p ~= ZMod 613` and `S/P ~= C/p`.

## The conductor argument

Mathlib's `conductor_mul_differentIdeal` (for the integral element `theta`) gives

  `(conductor Z theta) * differentIdeal Z C = span {aeval theta (P12')}`.

If a prime `P` above `613` contained the conductor, then
`aeval theta P12' ∈ P`.  On the other hand `P12(theta) = 0`, so the residue of
`theta` in the field `C/P` would be a common root of the reductions of `P12`
and `P12'` modulo `613`.  But S2580/S2582 give the explicit splitting of `P12`
modulo `613` into twelve distinct linear factors (roots
`21, 49, 154, 199, 224, 269` and their negatives), so `P12` is separable modulo
`613`; its reduction and that of its derivative generate the unit ideal.  This
contradiction shows that no prime above `613` contains the conductor, i.e.
`conductor + 613 C = C`.

Consequently `613` is a unit modulo the conductor.  If `613` divided the
exponent of the conductor (equivalently, if `613` were an element of the
conductor), then writing `exponent = 613 * m` would force `m` into the conductor
(still modulo the conductor) while `m < exponent`, contradicting the minimality
of the exponent (`RingOfIntegers.exponent_eq_sInf`).  Hence
`S2579Conductor613` holds.

Together with the linear residue factor `S2580LinearFactor613` this closes the
Kummer--Dedekind step of S2579 unconditionally.

No `sorry`, `axiom`, `True`, `native_decide` or opaque gate is used; the
axiom footprint is the usual `propext`, `Classical.choice`, `Quot.sound`.
-/

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual

open LeanFormal.IUT.XiFPaper.S2579Kummer613Actual
open LeanFormal.IUT.XiFPaper.S2581PrimitiveThetaActual
open LeanFormal.IUT.XiFPaper.S2582P12ClosedActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2580P12CertificateActual
open LeanFormal.IUT.XiFPaper.S2578Prime613Actual

local instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

/-! ## 1. The twelve distinct roots of P12 modulo 613 -/

/-- The twelve roots of `S2579P12` modulo `613`: for each of the six roots
`S2580r k` of the even sextic we take both signs. -/
def S2584root : Fin 6 × Bool → ZMod 613
  | (k, false) => S2580r k
  | (k, true) => -S2580r k

/-- The reduction of `S2579P12` modulo `613` is the product of the twelve linear
factors attached to the distinct roots `S2584root`. -/
theorem S2584_factorization :
    S2579P12.map (Int.castRingHom (ZMod 613)) =
      ∏ kb : Fin 6 × Bool, (X - C (S2584root kb)) := by
  rw [S2579P12_mod613_eq, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro k _
  rw [Fintype.prod_bool]
  simp only [S2584root]
  rw [Polynomial.C_neg, sub_neg_eq_add, mul_comm]

/-- The twelve roots are pairwise distinct modulo `613`. -/
theorem S2584_root_injective : Function.Injective S2584root := by
  rintro ⟨a, ba⟩ ⟨b, bb⟩ h
  fin_cases a <;> fin_cases b <;> cases ba <;> cases bb <;>
    simp only [S2584root, S2580r] at h ⊢
  all_goals first | rfl | (exfalso; revert h; decide)

/-- `S2579P12` is separable modulo `613`: it is a product of distinct linear
factors. -/
theorem S2584_p12map_separable :
    (S2579P12.map (Int.castRingHom (ZMod 613))).Separable := by
  rw [S2584_factorization]
  exact (Polynomial.separable_prod_X_sub_C_iff).mpr S2584_root_injective

/-- A Bezout identity modulo `613` between `P12` and its derivative. -/
theorem S2584_p12map_bezout :
    ∃ a b : (ZMod 613)[X],
      a * S2579P12.map (Int.castRingHom (ZMod 613)) +
        b * derivative (S2579P12.map (Int.castRingHom (ZMod 613))) = 1 :=
  (Polynomial.separable_def' _).mp S2584_p12map_separable

/-! ## 2. Primitivity and non-vanishing of the derivative at theta -/

/-- The primitivity statement of S2581, in the `Algebra.adjoin` form required by
`conductor_mul_differentIdeal`. -/
theorem S2584_hprim :
    Algebra.adjoin ℚ ({algebraMap C S1720Field S2579Theta} : Set S1720Field) = ⊤ := by
  have h := congrArg IntermediateField.toSubalgebra S2581_primitive
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (IsAlgebraic.of_finite ℚ (S2579Theta : S1720Field))] at h
  simpa using h

/-- The derivative of the minimal polynomial of `theta` does not vanish at
`theta` (separability in characteristic zero). -/
theorem S2584_haeval_ne :
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
theorem S2584_conductor_ne_bot : conductor ℤ S2579Theta ≠ ⊥ := by
  intro hbot
  have hmul := conductor_mul_differentIdeal (A := ℤ) (K := ℚ) (L := S1720Field)
    S2579Theta S2584_hprim
  have hspan : Ideal.span {aeval S2579Theta (derivative (minpoly ℤ S2579Theta))} = ⊥ := by
    rw [← hmul, hbot, Ideal.bot_mul]
  exact S2584_haeval_ne (Ideal.span_singleton_eq_bot.mp hspan)

/-- The exponent of the conductor is positive. -/
theorem S2584_exponent_pos : 0 < RingOfIntegers.exponent S2579Theta := by
  by_contra h
  have hzero : RingOfIntegers.exponent S2579Theta = 0 := Nat.eq_zero_of_not_pos h
  have hunder : Ideal.under ℤ (conductor ℤ S2579Theta) = ⊥ := by
    have habs : Ideal.absNorm (Ideal.under ℤ (conductor ℤ S2579Theta)) = 0 := by
      rw [show Ideal.absNorm (Ideal.under ℤ (conductor ℤ S2579Theta)) =
        RingOfIntegers.exponent S2579Theta from rfl, hzero]
    rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ (conductor ℤ S2579Theta)), habs]
    simp
  exact (Ideal.under_ne_bot (A := ℤ) S2584_conductor_ne_bot) hunder

/-! ## 3. No prime above 613 contains the conductor -/

/-- If a prime `P` above `613` contained the conductor, then the residue of
`theta` in the residue field would be a common root of `P12` and `P12'`
modulo `613`, contradicting the Bezout identity of `S2584_p12map_bezout`. -/
theorem S2584_no_prime_over613_le_conductor (P : Ideal C) [hPp : P.IsPrime]
    (hP : P.LiesOver (Ideal.span {(613 : ℤ)})) :
    ¬ conductor ℤ S2579Theta ≤ P := by
  intro hle
  have hmul := conductor_mul_differentIdeal (A := ℤ) (K := ℚ) (L := S1720Field)
    S2579Theta S2584_hprim
  have hmem : aeval S2579Theta (derivative (minpoly ℤ S2579Theta)) ∈ P := by
    have hspan : Ideal.span {aeval S2579Theta (derivative (minpoly ℤ S2579Theta))} ≤ P := by
      rw [← hmul]
      exact le_trans Ideal.mul_le_right hle
    exact (Ideal.span_singleton_le_iff_mem P).mp hspan
  rw [S2582_P12Certificate] at hmem
  let t : C ⧸ P := Ideal.Quotient.mk P S2579Theta
  let psi : ZMod 613 →+* (C ⧸ P) :=
    (algebraMap (ℤ ⧸ Ideal.span {(613 : ℤ)}) (C ⧸ P)).comp
      (Int.quotientSpanNatEquivZMod 613).symm.toRingHom
  letI : Algebra (ZMod 613) (C ⧸ P) := psi.toAlgebra
  have hcompat : psi.comp (Int.castRingHom (ZMod 613)) =
      (Ideal.Quotient.mk P).comp (algebraMap ℤ C) := by
    ext x
    change (algebraMap (ℤ ⧸ Ideal.span {(613 : ℤ)}) (C ⧸ P))
        ((Int.quotientSpanNatEquivZMod 613).symm (Int.castRingHom (ZMod 613) x))
      = (Ideal.Quotient.mk P) (algebraMap ℤ C x)
    have hx : (Int.quotientSpanNatEquivZMod 613).symm (Int.castRingHom (ZMod 613) x)
        = Ideal.Quotient.mk (Ideal.span {(613 : ℤ)}) x :=
      DFunLike.congr_fun (Int.quotientSpanNatEquivZMod_comp_castRingHom 613) x
    rw [hx]
    exact Ideal.Quotient.algebraMap_mk_of_liesOver P (Ideal.span {(613 : ℤ)}) x
  have hf0 :
      (S2579P12.map (Int.castRingHom (ZMod 613))).eval₂ psi t = 0 := by
    rw [Polynomial.eval₂_map, hcompat]
    have h := Polynomial.hom_eval₂ S2579P12 (algebraMap ℤ C) (Ideal.Quotient.mk P) S2579Theta
    rw [← h, ← Polynomial.aeval_def, S2580_aeval_Theta]
    simp
  have hf'0 :
      (derivative (S2579P12.map (Int.castRingHom (ZMod 613)))).eval₂ psi t = 0 := by
    rw [Polynomial.derivative_map, Polynomial.eval₂_map, hcompat]
    have h := Polynomial.hom_eval₂ (derivative S2579P12) (algebraMap ℤ C)
      (Ideal.Quotient.mk P) S2579Theta
    rw [← h, ← Polynomial.aeval_def]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  obtain ⟨a, b, hab⟩ := S2584_p12map_bezout
  have h1 := congrArg (fun p : (ZMod 613)[X] => p.eval₂ psi t) hab
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_one,
    hf0, hf'0, mul_zero, add_zero] at h1
  exact zero_ne_one h1

/-! ## 4. The conductor is comaximal with 613 -/

/-- No prime above `613` contains the conductor, so the conductor and `613 C`
generate the unit ideal. -/
theorem S2584_conductor_sup :
    conductor ℤ S2579Theta ⊔ Ideal.span {(613 : C)} = ⊤ := by
  by_contra hne
  obtain ⟨P, hPmax, hPle⟩ := Ideal.exists_le_maximal _ hne
  haveI hPp : P.IsPrime := hPmax.isPrime
  have h613 : (613 : C) ∈ P :=
    hPle (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton (613 : C))))
  have hPover : P.LiesOver (Ideal.span {(613 : ℤ)}) := by
    refine ⟨?_.symm⟩
    have hle : Ideal.span {(613 : ℤ)} ≤ P.under ℤ := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
      simpa using h613
    have hne_top : P.under ℤ ≠ ⊤ := by
      intro htop
      have h1 : (1 : ℤ) ∈ P.under ℤ := by rw [htop]; exact Submodule.mem_top
      rw [Ideal.under_def, Ideal.mem_comap] at h1
      have h2 : (1 : C) ∈ P := by simpa using h1
      exact hPmax.ne_top (Ideal.eq_top_iff_one P |>.mpr h2)
    exact (Int.ideal_span_isMaximal_of_prime 613).eq_of_le hne_top hle
  exact S2584_no_prime_over613_le_conductor P hPover (le_trans le_sup_left hPle)

/-- The last arithmetic input of S2579: `613` does not divide the exponent of
the conductor of `Z[theta]`. -/
theorem S2584_conductor613 : S2579Conductor613 := by
  unfold S2579Conductor613
  intro hdiv
  obtain ⟨m, hm⟩ := hdiv
  have hunit : IsUnit (Ideal.Quotient.mk (conductor ℤ S2579Theta) (613 : C)) := by
    have hsup := S2584_conductor_sup
    rw [Ideal.eq_top_iff_one] at hsup
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hsup
    rw [Ideal.mem_span_singleton] at hb
    obtain ⟨y, hy⟩ := hb
    have hmul1 : Ideal.Quotient.mk (conductor ℤ S2579Theta) (613 : C) *
        Ideal.Quotient.mk (conductor ℤ S2579Theta) y = 1 := by
      rw [← map_mul, ← hy]
      have hb1 : b = 1 - a := by linear_combination hab
      rw [hb1, map_sub, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr ha, sub_zero]
    exact isUnit_iff_exists.mpr ⟨_, hmul1, by rw [mul_comm]; exact hmul1⟩
  have hmpos : 0 < m := by
    have hpos := S2584_exponent_pos
    omega
  have hmlt : m < RingOfIntegers.exponent S2579Theta := by
    rw [hm]
    nlinarith [hmpos]
  have hexp_mem : (RingOfIntegers.exponent S2579Theta : C) ∈ conductor ℤ S2579Theta :=
    Int.absNorm_under_mem (conductor ℤ S2579Theta)
  have hm_mem : (m : C) ∈ conductor ℤ S2579Theta := by
    have h0 : Ideal.Quotient.mk (conductor ℤ S2579Theta) (m : C) = 0 := by
      have hprod : Ideal.Quotient.mk (conductor ℤ S2579Theta) (m : C) *
          Ideal.Quotient.mk (conductor ℤ S2579Theta) (613 : C) = 0 := by
        rw [← map_mul]
        have hcast : (m : C) * (613 : C) = (RingOfIntegers.exponent S2579Theta : C) := by
          rw [hm, Nat.cast_mul]
          ring
        rw [hcast, Ideal.Quotient.eq_zero_iff_mem.mpr hexp_mem]
      exact (IsUnit.mul_left_eq_zero hunit).mp hprod
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  have hle : RingOfIntegers.exponent S2579Theta ≤ m := by
    rw [RingOfIntegers.exponent_eq_sInf]
    exact Nat.sInf_le ⟨hmpos, hm_mem⟩
  omega

/-- The linear residue factor of S2580, restated for the S2579 interface. -/
theorem S2584_linearFactor613 : S2579LinearFactor613 := S2580LinearFactor613

/-- The headline Kummer--Dedekind consequence of S2579, now unconditional. -/
theorem S2584_prime613 :
    ∃ P : Ideal S, P.IsPrime ∧ P.LiesOver (Ideal.span {(613 : ℤ)}) ∧
      Nonempty (S ⧸ P ≃+* ZMod 613) :=
  S2579_prime613_of_arithmetic S2584_conductor613 S2584_linearFactor613

/-! ## 5. The actual prime of O_{F'} and its extension to S -/

/-- The data of a prime `p` of `O_{F'}` above `613` of inertia degree one, its
extension `P = p.map (algebraMap C S)` to `S`, and the residue identifications. -/
structure S2584PrimeDegreeOneWitness where
  p : Ideal C
  p_prime : p.IsPrime
  p_liesOver : p.LiesOver (Ideal.span {(613 : ℤ)})
  p_inertiaDeg : p.inertiaDeg ℤ = 1
  residueEquiv : C ⧸ p ≃+* ZMod 613
  P : Ideal S
  P_eq : P = p.map (algebraMap C S)
  P_prime : P.IsPrime
  P_liesOver_p : P.LiesOver p
  P_liesOver : P.LiesOver (Ideal.span {(613 : ℤ)})
  residueEquivS : S ⧸ P ≃+* ZMod 613
  quotientEquiv : S ⧸ P ≃+* C ⧸ p

/-- The witness exists: this is the requested actual `p`, `P` and residue
equivalences. -/
theorem S2584_witness_nonempty : Nonempty S2584PrimeDegreeOneWitness := by
  obtain ⟨r, hr⟩ := S2584_linearFactor613
  obtain ⟨p, hp_prime, hp_over, hp_deg⟩ :=
    S2579_linearFactor_prime S2579Theta S2584_conductor613 hr
  haveI : p.IsPrime := hp_prime
  obtain ⟨eO⟩ := S2579_quotient_equiv p hp_over hp_deg
  obtain ⟨P, hP_eq, hP_prime, hP_over, ⟨eS⟩⟩ :=
    S2579_localized_quotient_equiv p hp_over
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid C M : Set C) (p : Set C) :=
    S2578_disjoint p hp_prime hp_over
  have hP_lies_p : P.LiesOver p := by
    rw [hP_eq]
    exact IsLocalization.liesOver_map_of_isPrime_disjoint
      (M := Algebra.algebraMapSubmonoid C M) (S := S) hdisj
  exact ⟨{
    p := p
    p_prime := hp_prime
    p_liesOver := hp_over
    p_inertiaDeg := hp_deg
    residueEquiv := eO
    P := P
    P_eq := hP_eq
    P_prime := hP_prime
    P_liesOver_p := hP_lies_p
    P_liesOver := hP_over
    residueEquivS := eS.trans eO
    quotientEquiv := eS }⟩

/-- Existential consumer form of the witness. -/
theorem S2584_exists_primeDegreeOne :
    ∃ p : Ideal C, p.IsPrime ∧ p.LiesOver (Ideal.span {(613 : ℤ)}) ∧
      p.inertiaDeg ℤ = 1 ∧ Nonempty (C ⧸ p ≃+* ZMod 613) ∧
      ∃ P : Ideal S, P = p.map (algebraMap C S) ∧ P.IsPrime ∧
        P.LiesOver p ∧ P.LiesOver (Ideal.span {(613 : ℤ)}) ∧
        Nonempty (S ⧸ P ≃+* ZMod 613) ∧ Nonempty (S ⧸ P ≃+* C ⧸ p) := by
  obtain ⟨W⟩ := S2584_witness_nonempty
  exact ⟨W.p, W.p_prime, W.p_liesOver, W.p_inertiaDeg, ⟨W.residueEquiv⟩,
    W.P, W.P_eq, W.P_prime, W.P_liesOver_p, W.P_liesOver,
    ⟨W.residueEquivS⟩, ⟨W.quotientEquiv⟩⟩

/-! ## 6. Axiom footprint -/

#print axioms S2584_factorization
#print axioms S2584_p12map_separable
#print axioms S2584_p12map_bezout
#print axioms S2584_hprim
#print axioms S2584_haeval_ne
#print axioms S2584_conductor_ne_bot
#print axioms S2584_exponent_pos
#print axioms S2584_no_prime_over613_le_conductor
#print axioms S2584_conductor_sup
#print axioms S2584_conductor613
#print axioms S2584_prime613
#print axioms S2584_witness_nonempty
#print axioms S2584_exists_primeDegreeOne

end LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
end
