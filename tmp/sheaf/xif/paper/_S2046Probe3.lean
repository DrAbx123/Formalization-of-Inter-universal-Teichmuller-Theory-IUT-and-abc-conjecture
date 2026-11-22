import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.NumberTheory.Cyclotomic.Gal

open Polynomial

namespace S2046Probe

noncomputable def shiftEquiv (R : Type*) [CommRing R] : R[X] ≃+* R[X] where
  toFun p := p.comp (X + 1)
  invFun p := p.comp (X - 1)
  left_inv p := by
    rw [comp_assoc]
    simp
  right_inv p := by
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

example (n : Nat) :
    Irreducible (cyclotomic (p ^ (n + 1)) ℚ_[p]) := by
  let φ : ℤ →+* ℤ_[p] := Int.castRingHom ℤ_[p]
  let g : ℤ[X] := (cyclotomic (p ^ (n + 1)) ℤ).comp (X + 1)
  let F : ℤ_[p][X] := g.map φ
  have hEisInt : g.IsEisensteinAt (Ideal.span {(p : ℤ)}) :=
    cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p n
  have hweak : F.IsWeaklyEisensteinAt (Ideal.span {(p : ℤ_[p])}) := by
    have hmap := hEisInt.isWeaklyEisensteinAt.map φ
    simpa [F, g, φ, Ideal.map_span] using hmap
  have hmonic : F.Monic := by
    dsimp [F, g]
    exact (cyclotomic.monic _ ℤ).comp (monic_X_add_C 1) (by simp)
  have hne : Ideal.span {(p : ℤ_[p])} ≠ ⊤ := by
    intro htop
    have hpunit : IsUnit (p : ℤ_[p]) := by
      rw [Ideal.span_singleton_eq_top] at htop
      exact htop
    have hnorm := PadicInt.isUnit_iff.mp hpunit
    rw [PadicInt.norm_p] at hnorm
    have : (p : ℝ) ≠ 1 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_one
    exact (inv_eq_one.mp hnorm) (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt.ne')
  have hnot : F.coeff 0 ∉ (Ideal.span {(p : ℤ_[p])}) ^ 2 := by
    dsimp [F, g]
    rw [coeff_map]
    -- need transfer from hEisInt.notMem
    sorry
  have hEis : F.IsEisensteinAt (Ideal.span {(p : ℤ_[p])}) :=
    hmonic.isEisensteinAt_of_mem_of_notMem hne hweak.mem hnot
  have hprime : (Ideal.span {(p : ℤ_[p])}).IsPrime := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  have hdeg : 0 < F.natDegree := by
    dsimp [F, g]
    rw [natDegree_map_eq_of_injective (Int.castRingHom_injective)]
    rw [natDegree_comp, natDegree_X_add_C, Nat.mul_one, natDegree_cyclotomic]
    exact Nat.totient_pos.mpr (Nat.one_lt_pow (by decide) (Fact.out : Nat.Prime p).one_lt)
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
