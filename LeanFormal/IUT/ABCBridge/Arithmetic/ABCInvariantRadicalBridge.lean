import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantLocalValuations
import LeanFormal.IUT.Foundations.Arithmetic.Radical
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Radical comparison for the reduced ABC Frey/Legendre j-expression.

The exact prime-support comparison from the local-valuation module gives
`radical (2 * J.den) = radical (a*b*c)`. Thus using the reduced j-denominator
instead of the ABC product changes the radical by at most a factor of 2 and
its real logarithm by at most `log 2`. This arithmetic comparison does not
identify the denominator radical with a minimal elliptic conductor.
-/

namespace LeanFormal.IUT

theorem IsABCTriple.abcJInvariant_den_primeFactors_double {a b c : ℕ}
    (h : IsABCTriple a b c) :
    (2 * (abcJInvariant a b c).den).primeFactors = (a * b * c).primeFactors := by
  have hdenne : 2 * (abcJInvariant a b c).den ≠ 0 :=
    mul_ne_zero (by decide) (abcJInvariant a b c).den_nz
  have hproductne : a * b * c ≠ 0 := Nat.ne_of_gt h.abcInvariant_product_pos
  apply Finset.ext
  intro p
  rw [Nat.mem_primeFactors, Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hdiv, _⟩
    letI : Fact p.Prime := ⟨hp⟩
    exact ⟨hp, h.prime_dvd_twice_abcJInvariant_den_iff.mp hdiv, hproductne⟩
  · rintro ⟨hp, hdiv, _⟩
    letI : Fact p.Prime := ⟨hp⟩
    exact ⟨hp, h.prime_dvd_twice_abcJInvariant_den_iff.mpr hdiv, hdenne⟩

theorem IsABCTriple.abcJInvariant_den_radical_double {a b c : ℕ}
    (h : IsABCTriple a b c) :
    radical (2 * (abcJInvariant a b c).den) = radical (a * b * c) := by
  change natRadical (2 * (abcJInvariant a b c).den) = natRadical (a * b * c)
  simp only [natRadical_eq_prod_primeFactors, h.abcJInvariant_den_primeFactors_double]

theorem abcInvariant_natRadical_double_le_twice {n : ℕ} (hnne : n ≠ 0) :
    natRadical (2 * n) ≤ 2 * natRadical n := by
  by_cases hdiv : 2 ∣ n
  · have hdivsquare : 2 * n ∣ n ^ 2 := by
      obtain ⟨k, hk⟩ := hdiv
      refine ⟨k, ?_⟩
      rw [hk]
      ring
    have hraddiv := natRadical_dvd_radical_of_dvd hdivsquare (pow_ne_zero 2 hnne)
    rw [natRadical_pow (by decide : (2 : ℕ) ≠ 0)] at hraddiv
    have hle : natRadical (2 * n) ≤ natRadical n :=
      Nat.le_of_dvd (natRadical_pos n) hraddiv
    omega
  · have hcoprime : Nat.Coprime 2 n := by
      by_contra hnotcoprime
      exact hdiv (Nat.prime_two.dvd_iff_not_coprime.mpr hnotcoprime)
    rw [natRadical_mul_of_coprime hcoprime]
    have htwo : natRadical 2 ≤ 2 := Nat.le_of_dvd (by decide) natRadical_dvd_self
    exact Nat.mul_le_mul_right (natRadical n) htwo

theorem IsABCTriple.abcJInvariant_den_radical_le_product {a b c : ℕ}
    (h : IsABCTriple a b c) :
    radical (abcJInvariant a b c).den ≤ radical (a * b * c) := by
  have hdiv : (abcJInvariant a b c).den ∣ 2 * (abcJInvariant a b c).den := by
    exact ⟨2, by ring⟩
  have hne : 2 * (abcJInvariant a b c).den ≠ 0 :=
    mul_ne_zero (by decide) (abcJInvariant a b c).den_nz
  have hraddiv := natRadical_dvd_radical_of_dvd hdiv hne
  have hle := Nat.le_of_dvd (natRadical_pos (2 * (abcJInvariant a b c).den)) hraddiv
  change radical (abcJInvariant a b c).den ≤
    radical (2 * (abcJInvariant a b c).den) at hle
  rw [h.abcJInvariant_den_radical_double] at hle
  exact hle

theorem IsABCTriple.abcInvariant_product_radical_le_twice_den {a b c : ℕ}
    (h : IsABCTriple a b c) :
    radical (a * b * c) ≤ 2 * radical (abcJInvariant a b c).den := by
  rw [← h.abcJInvariant_den_radical_double]
  exact abcInvariant_natRadical_double_le_twice (abcJInvariant a b c).den_nz

theorem IsABCTriple.abcJInvariant_den_radical_bounds {a b c : ℕ}
    (h : IsABCTriple a b c) :
    radical (abcJInvariant a b c).den ≤ radical (a * b * c) ∧
      radical (a * b * c) ≤ 2 * radical (abcJInvariant a b c).den := by
  exact ⟨h.abcJInvariant_den_radical_le_product,
    h.abcInvariant_product_radical_le_twice_den⟩

theorem IsABCTriple.abcJInvariant_den_logRadical_double {a b c : ℕ}
    (h : IsABCTriple a b c) :
    Real.log (radical (2 * (abcJInvariant a b c).den) : ℝ) =
      Real.log (radical (a * b * c) : ℝ) := by
  rw [h.abcJInvariant_den_radical_double]

theorem IsABCTriple.abcJInvariant_den_logRadical_le_product {a b c : ℕ}
    (h : IsABCTriple a b c) :
    Real.log (radical (abcJInvariant a b c).den : ℝ) ≤
      Real.log (radical (a * b * c) : ℝ) := by
  apply Real.log_le_log
  · exact_mod_cast natRadical_pos (abcJInvariant a b c).den
  · exact_mod_cast h.abcJInvariant_den_radical_le_product

theorem IsABCTriple.abcInvariant_product_logRadical_le_den_add_log_two
    {a b c : ℕ} (h : IsABCTriple a b c) :
    Real.log (radical (a * b * c) : ℝ) ≤
      Real.log (radical (abcJInvariant a b c).den : ℝ) + Real.log 2 := by
  have hproductpos : (0 : ℝ) < (radical (a * b * c) : ℝ) := by
    exact_mod_cast natRadical_pos (a * b * c)
  have hdenpos : (0 : ℝ) < (radical (abcJInvariant a b c).den : ℝ) := by
    exact_mod_cast natRadical_pos (abcJInvariant a b c).den
  have hupper : (radical (a * b * c) : ℝ) ≤
      2 * (radical (abcJInvariant a b c).den : ℝ) := by
    exact_mod_cast h.abcInvariant_product_radical_le_twice_den
  calc
    Real.log (radical (a * b * c) : ℝ) ≤
        Real.log (2 * (radical (abcJInvariant a b c).den : ℝ)) :=
      Real.log_le_log hproductpos hupper
    _ = Real.log (radical (abcJInvariant a b c).den : ℝ) + Real.log 2 := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hdenpos)]
      ring

theorem IsABCTriple.abcJInvariant_den_logRadical_bounds {a b c : ℕ}
    (h : IsABCTriple a b c) :
    Real.log (radical (abcJInvariant a b c).den : ℝ) ≤
        Real.log (radical (a * b * c) : ℝ) ∧
      Real.log (radical (a * b * c) : ℝ) ≤
        Real.log (radical (abcJInvariant a b c).den : ℝ) + Real.log 2 := by
  exact ⟨h.abcJInvariant_den_logRadical_le_product,
    h.abcInvariant_product_logRadical_le_den_add_log_two⟩

theorem IsABCTriple.abcJInvariant_den_logRadical_difference_bounds
    {a b c : ℕ} (h : IsABCTriple a b c) :
    0 ≤ Real.log (radical (a * b * c) : ℝ) -
        Real.log (radical (abcJInvariant a b c).den : ℝ) ∧
      Real.log (radical (a * b * c) : ℝ) -
        Real.log (radical (abcJInvariant a b c).den : ℝ) ≤ Real.log 2 := by
  have hlower := h.abcJInvariant_den_logRadical_le_product
  have hupper := h.abcInvariant_product_logRadical_le_den_add_log_two
  constructor <;> linarith

end LeanFormal.IUT
