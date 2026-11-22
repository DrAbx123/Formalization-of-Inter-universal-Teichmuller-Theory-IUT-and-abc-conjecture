/-
# IUT IV Prop 1.3 (i): the different estimate in a tower (inequality part)

Paper (IUT IV L568–583): for finite extensions `k_0 ⊆ k_i` of `ℚ_p`, writing `d_i` for the
order of the different of `k_i / ℚ_p` normalized so that `ord(p) = 1`, and `e_{i/0}`, `e_i`
for the ramification indices of `k_i / k_0` and `k_i / ℚ_p`,

  `d_i ≥ d_0 + (e_{i/0} - 1) / e_i`

(with equality if `k_i / k_0` is tamely ramified).

This file proves the inequality for an arbitrary tower of Dedekind domains `A ⊆ B ⊆ C` at a
chain of nonzero primes `p ⊆ Q ⊆ P`: the rings of integers `ℤ_p ⊆ 𝒪_{k_0} ⊆ 𝒪_{k_i}` are a
special case (`p = (p)`, `e(Q|p) = e_0`, `e(P|p) = e_i`).  Ingredients are all in Mathlib:
transitivity of the different (`differentIdeal_eq_differentIdeal_mul_differentIdeal`),
Dedekind's bound `P^(e-1) ∣ 𝔇` (`pow_sub_one_dvd_differentIdeal`), the multiplicity of `P` in
an extended ideal (`emultiplicity_map_eq_ramificationIdx'_mul`) and multiplicativity of `e` in
towers (`ramificationIdx'_algebra_tower`).

The tame equality case is proved in `DifferentTameEquality.lean`; Prop 1.3 (ii) is not proved.
-/

import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.Data.Real.Basic

open Ideal UniqueFactorizationMonoid Module

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace LeanFormal.IUT.IUTIV.Estimates

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
  [IsDedekindDomain A] [IsDedekindDomain B] [IsDedekindDomain C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [Module.Finite A B] [Module.Finite A C] [Module.Finite B C]
  [IsTorsionFree A B] [IsTorsionFree A C] [IsTorsionFree B C]
  [Algebra.IsSeparable (FractionRing A) (FractionRing C)]

/-- **Different multiplicity in a tower.**  For nonzero primes `P` of `C` over `Q` of `B`:
`ord_P 𝔇_{C/A} = ord_P 𝔇_{C/B} + e(P|Q) · ord_Q 𝔇_{B/A}`. -/
theorem count_differentIdeal_tower [DecidableEq (Ideal B)] [DecidableEq (Ideal C)]
    (Q : Ideal B) (P : Ideal C) [Q.IsPrime] [P.IsPrime] (hQ : Q ≠ ⊥) (hP : P ≠ ⊥)
    [P.LiesOver Q] :
    (normalizedFactors (differentIdeal A C)).count P =
      (normalizedFactors (differentIdeal B C)).count P +
        ramificationIdx' Q P * (normalizedFactors (differentIdeal A B)).count Q := by
  have : Algebra.IsSeparable (FractionRing B) (FractionRing C) :=
    Algebra.isSeparable_tower_top_of_isSeparable (FractionRing A) _ _
  have : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    Algebra.isSeparable_tower_bot_of_isSeparable _ _ (FractionRing C)
  have hPirr : Irreducible P := (Ideal.prime_of_isPrime hP inferInstance).irreducible
  have hQirr : Irreducible Q := (Ideal.prime_of_isPrime hQ inferInstance).irreducible
  have hAB : differentIdeal A B ≠ ⊥ := differentIdeal_ne_bot
  have hBC : differentIdeal B C ≠ ⊥ := differentIdeal_ne_bot
  have hAC : differentIdeal A C ≠ ⊥ := differentIdeal_ne_bot
  have hmap : (differentIdeal A B).map (algebraMap B C) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hAB
  have htrans := differentIdeal_eq_differentIdeal_mul_differentIdeal A B C
  have hemul : emultiplicity P (differentIdeal A C) =
      emultiplicity P (differentIdeal B C) +
        ramificationIdx' Q P * emultiplicity Q (differentIdeal A B) := by
    rw [htrans, emultiplicity_mul hPirr.prime,
      Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul hAB hQirr hPirr hP]
  rw [emultiplicity_eq_count_normalizedFactors hPirr hAC,
    emultiplicity_eq_count_normalizedFactors hPirr hBC,
    emultiplicity_eq_count_normalizedFactors hQirr hAB,
    normalize_eq, normalize_eq] at hemul
  exact_mod_cast hemul

omit [Algebra.IsSeparable (FractionRing A) (FractionRing C)] in
/-- **Dedekind's bound in multiplicity form.**  `ord_P 𝔇_{C/B} ≥ e(P|Q) - 1`. -/
theorem ramificationIdx'_sub_one_le_count_differentIdeal [DecidableEq (Ideal C)]
    [Algebra.IsSeparable (FractionRing B) (FractionRing C)]
    (Q : Ideal B) (P : Ideal C) [Q.IsPrime] [P.IsPrime] (hQ : Q ≠ ⊥) (hP : P ≠ ⊥)
    [P.LiesOver Q] :
    ramificationIdx' Q P - 1 ≤ (normalizedFactors (differentIdeal B C)).count P := by
  haveI : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQ
  have hPirr : Irreducible P := (Ideal.prime_of_isPrime hP inferInstance).irreducible
  have hBC : differentIdeal B C ≠ ⊥ := differentIdeal_ne_bot
  have hdvd : P ^ ramificationIdx' Q P ∣ Q.map (algebraMap B C) :=
    Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx'
  have h := pow_sub_one_dvd_differentIdeal B P (ramificationIdx' Q P) hQ hdvd
  have hle := (pow_dvd_iff_le_emultiplicity).mp h
  rw [emultiplicity_eq_count_normalizedFactors hPirr hBC, normalize_eq] at hle
  exact_mod_cast hle

/-- **IUT IV Prop 1.3 (i), inequality part, for a Dedekind tower.**  With the normalized
different orders `d_B := ord_Q 𝔇_{B/A} / e(Q|p)` and `d_C := ord_P 𝔇_{C/A} / e(P|p)`,

  `d_C ≥ d_B + (e(P|Q) - 1) / e(P|p)`. -/
theorem iutIVProp13i_normalizedDifferent_ge [DecidableEq (Ideal B)] [DecidableEq (Ideal C)]
    (p : Ideal A) (Q : Ideal B) (P : Ideal C) [p.IsPrime] [Q.IsPrime] [P.IsPrime]
    (hp : p ≠ ⊥) (hQ : Q ≠ ⊥) (hP : P ≠ ⊥) [Q.LiesOver p] [P.LiesOver Q] [P.LiesOver p] :
    ((normalizedFactors (differentIdeal A B)).count Q : ℝ) / ramificationIdx' p Q +
        ((ramificationIdx' Q P : ℝ) - 1) / ramificationIdx' p P ≤
      ((normalizedFactors (differentIdeal A C)).count P : ℝ) / ramificationIdx' p P := by
  have htower : ramificationIdx' p P = ramificationIdx' p Q * ramificationIdx' Q P := by
    apply ramificationIdx'_algebra_tower
    · exact Ideal.map_ne_bot_of_ne_bot hQ
    · exact Ideal.map_ne_bot_of_ne_bot hp
    · exact Ideal.map_le_iff_le_comap.mpr (le_of_eq (Ideal.over_def P Q))
  have heQ : ramificationIdx' p Q ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver Q hp
  have hePQ : ramificationIdx' Q P ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver P hQ
  have hcount := count_differentIdeal_tower A B C Q P hQ hP
  have : Algebra.IsSeparable (FractionRing B) (FractionRing C) :=
    Algebra.isSeparable_tower_top_of_isSeparable (FractionRing A) _ _
  have hdedekind := ramificationIdx'_sub_one_le_count_differentIdeal B C Q P hQ hP
  set eQ := ramificationIdx' p Q
  set ePQ := ramificationIdx' Q P
  set dAB := (normalizedFactors (differentIdeal A B)).count Q
  set dBC := (normalizedFactors (differentIdeal B C)).count P
  set dAC := (normalizedFactors (differentIdeal A C)).count P
  have heQr : (0 : ℝ) < eQ := by exact_mod_cast Nat.pos_of_ne_zero heQ
  have hePQr : (0 : ℝ) < ePQ := by exact_mod_cast Nat.pos_of_ne_zero hePQ
  have hdBC : (ePQ : ℝ) - 1 ≤ dBC := by
    have : ePQ ≤ dBC + 1 := by omega
    have : (ePQ : ℝ) ≤ dBC + 1 := by exact_mod_cast this
    linarith
  rw [htower, hcount]
  push_cast
  rw [div_add_div _ _ heQr.ne' (mul_pos heQr hePQr).ne', div_le_div_iff₀
    (mul_pos heQr (mul_pos heQr hePQr)) (mul_pos heQr hePQr)]
  nlinarith [mul_le_mul_of_nonneg_left hdBC (mul_pos heQr heQr).le]

end LeanFormal.IUT.IUTIV.Estimates
