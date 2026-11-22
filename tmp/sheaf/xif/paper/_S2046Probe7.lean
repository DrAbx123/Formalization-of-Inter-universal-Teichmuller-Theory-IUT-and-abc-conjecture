import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Totient

open Polynomial

namespace S2046Probe

noncomputable def shiftEquiv (R : Type*) [CommRing R] : R[X] ≃+* R[X] where
  toFun p := p.comp (X + 1)
  invFun p := p.comp (X - 1)
  left_inv p := by
    change (p.comp (X + 1)).comp (X - 1) = p
    rw [comp_assoc]
    simp
  right_inv p := by
    change (p.comp (X - 1)).comp (X + 1) = p
    rw [comp_assoc]
    simp
  map_mul' p q := by simp
  map_add' p q := by simp

theorem irreducible_of_comp_X_add_one {R : Type*} [CommRing R] {f : R[X]}
    (h : Irreducible (f.comp (X + 1))) : Irreducible f := by
  let e : R[X] ≃* R[X] := (shiftEquiv R).toMulEquiv
  have h' : Irreducible (e f) := by simpa [e, shiftEquiv] using h
  exact (MulEquiv.irreducible_iff (f := e) (x := f)).mp h'

variable (p : Nat) [Fact (Nat.Prime p)]

lemma irreducible_cyclotomic_prime_pow_padic (n : Nat) :
    Irreducible (cyclotomic (p ^ (n + 1)) ℚ_[p]) := by
  haveI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero⟩
  let φ : ℤ →+* ℤ_[p] := Int.castRingHom ℤ_[p]
  let g : ℤ[X] := (cyclotomic (p ^ (n + 1)) ℤ).comp (X + 1)
  let F : ℤ_[p][X] := g.map φ
  have hEisInt : g.IsEisensteinAt (Ideal.span {(p : ℤ)}) :=
    cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p n
  have hweak : F.IsWeaklyEisensteinAt (Ideal.span {(p : ℤ_[p])}) := by
    have hmap := hEisInt.isWeaklyEisensteinAt.map φ
    simpa [F, g, φ, Ideal.map_span] using hmap
  have hgmonic : g.Monic := by
    dsimp [g]
    exact (cyclotomic.monic _ ℤ).comp (monic_X_add_C 1) (by
      rw [show (X + 1 : ℤ[X]) = X + C 1 by simp]
      rw [natDegree_X_add_C]
      exact one_ne_zero)
  have hmonic : F.Monic := hgmonic.map φ
  have hmax : (Ideal.span {(p : ℤ_[p])}).IsMaximal := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  have hne : Ideal.span {(p : ℤ_[p])} ≠ ⊤ := hmax.ne_top
  have hnot_int : ¬ (p : ℤ) ^ 2 ∣ g.coeff 0 := by
    intro hd
    apply hEisInt.notMem
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hd
  have hnot : F.coeff 0 ∉ (Ideal.span {(p : ℤ_[p])}) ^ 2 := by
    dsimp [F]
    rw [coeff_map]
    intro hmem
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    have ha : (g.coeff 0 : ℤ_[p]) ≠ 0 := by
      intro h0
      apply hnot_int
      have : g.coeff 0 = 0 := Int.cast_injective h0
      rw [this]
      exact dvd_zero _
    have hmem_span : (g.coeff 0 : ℤ_[p]) ∈
        (Ideal.span {(p : ℤ_[p]) ^ 2}) := by
      rw [Ideal.mem_span_singleton]
      exact hmem
    have hle : 2 ≤ (g.coeff 0 : ℤ_[p]).valuation :=
      (PadicInt.mem_span_pow_iff_le_valuation _ ha 2).mp hmem_span
    have hpadic : 2 ≤ padicValInt p (g.coeff 0) := by
      simpa [PadicInt.valuation, Padic.valuation_intCast] using hle
    exact hnot_int ((padicValInt_dvd_iff 2 (g.coeff 0)).mpr (Or.inr hpadic))
  have hEis : F.IsEisensteinAt (Ideal.span {(p : ℤ_[p])}) :=
    hmonic.isEisensteinAt_of_mem_of_notMem hne hweak.mem hnot
  have hprime : (Ideal.span {(p : ℤ_[p])}).IsPrime := hmax.isPrime
  have hdeg : 0 < F.natDegree := by
    dsimp [F]
    rw [natDegree_map_eq_of_injective Int.cast_injective]
    dsimp [g]
    rw [natDegree_comp,
      show (X + 1 : ℤ[X]) = X + C 1 by simp,
      natDegree_X_add_C, mul_one, natDegree_cyclotomic]
    exact Nat.totient_pos.mpr (Nat.one_lt_pow (Nat.succ_ne_zero n) (Fact.out : Nat.Prime p).one_lt).pos
  have hirrF : Irreducible F := hEis.irreducible hprime hmonic.isPrimitive hdeg
  have hcomp : F = (cyclotomic (p ^ (n + 1)) ℤ_[p]).comp (X + 1) := by
    dsimp [F, g]
    rw [map_comp, map_cyclotomic]
    simp
  have hirr_shift : Irreducible ((cyclotomic (p ^ (n + 1)) ℤ_[p]).comp (X + 1)) := by
    rwa [← hcomp]
  have hirr_int : Irreducible (cyclotomic (p ^ (n + 1)) ℤ_[p]) :=
    irreducible_of_comp_X_add_one hirr_shift
  have hprim : (cyclotomic (p ^ (n + 1)) ℤ_[p]).IsPrimitive :=
    (cyclotomic.monic _ _).isPrimitive
  have := (hprim.irreducible_iff_irreducible_map_fraction_map (K := ℚ_[p])).mp hirr_int
  simpa [map_cyclotomic] using this

end S2046Probe
