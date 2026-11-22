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

noncomputable def unitPartValue (x : ℚ_[p]ˣ) : ℚ_[p] :=
  x.val * (p : ℚ_[p]) ^ (-(x.val.valuation) : ℤ)

lemma norm_unitPartValue (x : ℚ_[p]ˣ) : ‖unitPartValue p x‖ = 1 := by
  rw [unitPartValue, norm_mul, Padic.norm_eq_zpow_neg_valuation (Units.ne_zero x),
    Padic.norm_p_zpow]
  rw [← zpow_add₀]
  · simp
  · exact_mod_cast (Fact.out : Nat.Prime p).ne_zero

noncomputable def unitPart (x : ℚ_[p]ˣ) : ℤ_[p]ˣ :=
  PadicInt.mkUnits (norm_unitPartValue p x)

lemma unitPart_coe (x : ℚ_[p]ˣ) :
    ((unitPart p x : ℤ_[p]) : ℚ_[p]) = unitPartValue p x :=
  PadicInt.mkUnits_eq (norm_unitPartValue p x)

lemma unitPart_mul_coe (x y : ℚ_[p]ˣ) :
    ((unitPart p (x * y) : ℤ_[p]) : ℚ_[p]) =
      ((unitPart p x : ℤ_[p]) : ℚ_[p]) * ((unitPart p y : ℤ_[p]) : ℚ_[p]) := by
  rw [unitPart_coe, unitPart_coe, unitPart_coe, unitPartValue, unitPartValue, unitPartValue,
    Units.val_mul, Padic.valuation_mul (Units.ne_zero x) (Units.ne_zero y), neg_add,
    zpow_add₀]
  · ring
  · exact_mod_cast (Fact.out : Nat.Prime p).ne_zero

noncomputable def unitPartHom : ℚ_[p]ˣ →* ℤ_[p]ˣ where
  toFun := unitPart p
  map_one' := by
    ext
    apply PadicInt.ext
    rw [unitPart_coe]
    simp [unitPartValue, Padic.valuation_one]
  map_mul' x y := by
    ext
    apply PadicInt.ext
    exact unitPart_mul_coe p x y

abbrev CyclotomicLevel (n : Nat) : Type := CyclotomicField (p ^ (n + 1)) ℚ_[p]

instance cyclotomicLevelCyclotomic (n : Nat) :
    IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] (CyclotomicLevel p n) := by
  dsimp [CyclotomicLevel]
  infer_instance

noncomputable def unitPartMod (n : Nat) : ℚ_[p]ˣ →* (ZMod (p ^ n))ˣ :=
  (Units.map (PadicInt.toZModPow n).toMonoidHom).comp (unitPartHom p)

noncomputable def cycRec (n : Nat) :
    ℚ_[p]ˣ →* Gal(CyclotomicLevel p n / ℚ_[p]) := by
  letI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero⟩
  exact (IsCyclotomicExtension.autEquivPow (CyclotomicLevel p n)
    (irreducible_cyclotomic_prime_pow_padic p n)).symm.toMonoidHom.comp
      (unitPartMod p (n + 1))

lemma cycRec_zeta (n : Nat) (x : ℚ_[p]ˣ) :
    cycRec p n x (IsCyclotomicExtension.zeta (p ^ (n + 1)) ℚ_[p] (CyclotomicLevel p n)) =
      (IsCyclotomicExtension.zeta (p ^ (n + 1)) ℚ_[p] (CyclotomicLevel p n)) ^
        (ZMod.val ((unitPartMod p (n + 1) x : (ZMod (p ^ (n + 1)))ˣ) : ZMod (p ^ (n + 1)))) := by
  letI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero⟩
  have h := IsPrimitiveRoot.autToPow_spec (R := ℚ_[p])
    (hμ := IsCyclotomicExtension.zeta_spec (p ^ (n + 1)) ℚ_[p] (CyclotomicLevel p n))
    (f := cycRec p n x)
  rw [← h]
  congr 1
  have hu : (IsCyclotomicExtension.autEquivPow (CyclotomicLevel p n)
      (irreducible_cyclotomic_prime_pow_padic p n)) (cycRec p n x) =
      unitPartMod p (n + 1) x := by
    simp [cycRec]
  exact congrArg Units.val hu

end S2046Probe
