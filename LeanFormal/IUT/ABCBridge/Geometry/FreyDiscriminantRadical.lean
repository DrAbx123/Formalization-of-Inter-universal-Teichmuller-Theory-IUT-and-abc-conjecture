import LeanFormal.IUT.ABCBridge.Geometry.FreyWeierstrassCurve
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantLocalValuations
import LeanFormal.IUT.Foundations.Arithmetic.Radical
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

/-!
# Radical identification for the Frey discriminant of an ABC triple

For an actual ABC triple `h : IsABCTriple a b c`, the natural-number form
`16 * a ^ 2 * b ^ 2 * c ^ 2` of the discriminant of the Frey curve
`rationalFreyWeierstrassCurve a b` (see
`rationalFreyWeierstrassCurve_discriminant_natCast_sixteen_mul_sq_of_isABCTriple`) has the same
radical as the product `a * b * c`, and a prime divides one exactly when it
divides the other:

`natRadical (16 * a ^ 2 * b ^ 2 * c ^ 2) = natRadical (a * b * c)`,
`p.Prime → (p ∣ natRadical (16 * a ^ 2 * b ^ 2 * c ^ 2) ↔ p ∣ a * b * c)`.

The mechanism is elementary: every ABC triple satisfies `2 ∣ a * b * c`
(`IsABCTriple.two_dvd_abcInvariant_product`), so the coefficient `16 = 2 ^ 4`
contributes no prime to the radical of `(a * b * c) ^ 2`; the auxiliary
statement `natRadical (16 * t ^ 2) = natRadical t` for even `t` is proved from
the prime-factor sets.

## Scope

This file covers only the radical layer (gap G4 of the conductor/height
reconnaissance).  It does **not** prove the Tate-algorithm relation
`ord_p (Δ) = ord_p (N_E) + correction`, because the local conductor exponents
and a conductor API are not available in this repository.  It does not identify
the conductor of the Frey curve, its minimal model, or semistability, and it
makes no comparison with an IUT theta construction.  "Discriminant" below refers
only to the discriminant formula proved in
`LeanFormal.IUT.ABCBridge.Geometry.FreyWeierstrassCurve`.
-/

namespace LeanFormal.IUT

/-! ### 1. The auxiliary radical computation for even `t` -/

/-- For even `t`, the coefficient `16 = 2 ^ 4` contributes only the prime `2`
to `16 * t ^ 2`, and `2` already divides `t`; hence the prime factors of
`16 * t ^ 2` are exactly the prime factors of `t`. -/
theorem primeFactors_sixteen_mul_square_of_two_dvd {t : ℕ} (h2 : 2 ∣ t) :
    (16 * t ^ 2).primeFactors = t.primeFactors := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  have h2mem : 2 ∈ t.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, ht⟩
  have h16 : (16 : ℕ).primeFactors = {2} := by
    have hpow : (16 : ℕ) = 2 ^ 4 := by norm_num
    rw [hpow, Nat.primeFactors_prime_pow (by norm_num : (4 : ℕ) ≠ 0) Nat.prime_two]
  calc
    (16 * t ^ 2).primeFactors
        = (16 : ℕ).primeFactors ∪ (t ^ 2).primeFactors :=
          Nat.primeFactors_mul (by norm_num : (16 : ℕ) ≠ 0) (pow_ne_zero 2 ht)
    _ = {2} ∪ t.primeFactors := by
          rw [h16, Nat.primeFactors_pow t (by norm_num : (2 : ℕ) ≠ 0)]
    _ = t.primeFactors :=
          (Finset.union_eq_right).mpr (Finset.singleton_subset_iff.mpr h2mem)

/-- For even `t`, the radicals of `16 * t ^ 2` and `t` agree; this is the
radical form of `primeFactors_sixteen_mul_square_of_two_dvd`. -/
theorem natRadical_sixteen_mul_square_of_two_dvd {t : ℕ} (h2 : 2 ∣ t) :
    natRadical (16 * t ^ 2) = natRadical t := by
  simp only [natRadical_eq_prod_primeFactors, primeFactors_sixteen_mul_square_of_two_dvd h2]

/-! ### 2. The discriminant of the Frey curve in its natural-number form -/

/-- For an actual ABC triple, the discriminant of the rational Frey curve
`rationalFreyWeierstrassCurve a b` is the cast of the natural number
`16 * a ^ 2 * b ^ 2 * c ^ 2`.  This identification is what the radical results
below are about; it carries no minimality or conductor claim. -/
theorem rationalFreyWeierstrassCurve_discriminant_natCast_sixteen_mul_sq_of_isABCTriple
    {a b c : ℕ}
    (h : IsABCTriple a b c) :
    (rationalFreyWeierstrassCurve a b).Δ = ((16 * a ^ 2 * b ^ 2 * c ^ 2 : ℕ) : ℚ) := by
  rw [rationalFreyWeierstrassCurve_discriminant_of_isABCTriple h]
  push_cast
  ring

/-! ### 3. The radical identification and the prime-support bridge -/

/-- For an actual ABC triple, the radical of the natural-number Frey
discriminant `16 * a ^ 2 * b ^ 2 * c ^ 2` equals the radical of `a * b * c`:
the coefficient `16 = 2 ^ 4` adds only the prime `2`, and `2 ∣ a * b * c`. -/
theorem IsABCTriple.natRadical_freyDiscriminant_eq_natRadical_product {a b c : ℕ}
    (h : IsABCTriple a b c) :
    natRadical (16 * a ^ 2 * b ^ 2 * c ^ 2) = natRadical (a * b * c) := by
  have hsquare : 16 * a ^ 2 * b ^ 2 * c ^ 2 = 16 * (a * b * c) ^ 2 := by ring
  rw [hsquare]
  exact natRadical_sixteen_mul_square_of_two_dvd h.two_dvd_abcInvariant_product

/-- Prime-support form of the radical identification: the prime factors of the
natural-number Frey discriminant and of the product `a * b * c` agree. -/
theorem IsABCTriple.primeFactors_freyDiscriminant_eq {a b c : ℕ}
    (h : IsABCTriple a b c) :
    (16 * a ^ 2 * b ^ 2 * c ^ 2).primeFactors = (a * b * c).primeFactors := by
  have hsquare : 16 * a ^ 2 * b ^ 2 * c ^ 2 = 16 * (a * b * c) ^ 2 := by ring
  rw [hsquare]
  exact primeFactors_sixteen_mul_square_of_two_dvd h.two_dvd_abcInvariant_product

/-- A prime divides `natRadical n` exactly when it divides `n` (for `n ≠ 0`;
at `n = 0` the forward implication fails because `natRadical 0 = 1`). -/
theorem prime_dvd_natRadical_iff {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    p ∣ natRadical n ↔ p ∣ n := by
  constructor
  · intro hdiv
    exact hdiv.trans natRadical_dvd_self
  · intro hdiv
    rw [natRadical_eq_prod_primeFactors]
    exact Finset.dvd_prod_of_mem id (Nat.mem_primeFactors.mpr ⟨hp, hdiv, hn⟩)

/-- Bridge corollary for prime-support consumers: a prime divides the radical
of the Frey discriminant `16 * a ^ 2 * b ^ 2 * c ^ 2` if and only if it divides
the product `a * b * c`. -/
theorem IsABCTriple.prime_dvd_natRadical_freyDiscriminant_iff {a b c p : ℕ}
    (h : IsABCTriple a b c) (hp : p.Prime) :
    p ∣ natRadical (16 * a ^ 2 * b ^ 2 * c ^ 2) ↔ p ∣ a * b * c := by
  rw [h.natRadical_freyDiscriminant_eq_natRadical_product]
  exact prime_dvd_natRadical_iff hp (Nat.ne_of_gt h.abcInvariant_product_pos)

end LeanFormal.IUT
