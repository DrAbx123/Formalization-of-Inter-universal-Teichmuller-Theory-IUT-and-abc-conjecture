import LeanFormal.IUT.ABCBridge.Geometry.FreyOddReduction
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCNonemptyOddBadSupport

/-!
# Odd-part conductor exponents of the ABC Frey curve

This file packages the odd-prime reduction classification proved in
`LeanFormal.IUT.ABCBridge.Geometry.FreyOddReduction` into

* a named local odd conductor exponent `conductorExponentOdd`, read off from
  good / multiplicative reduction of a Weierstrass model over `ℚ_[p]`, and
* a global odd-part conductor `oddConductor E` of a Weierstrass model over `ℚ`,
  defined as the finite product of `p ^ conductorExponentOdd p E` over the odd
  prime divisors of the rational discriminant of the model,

and identifies `oddConductor (rationalFreyWeierstrassCurve a b)` with the odd
radical of `a * b * c` for every actual ABC triple (`frey_oddConductor_eq_oddRadical`).

## Proved / unproved boundary

* **Proved.** `freyPadicCurve_conductorExponentOdd_of_dvd` and
  `freyPadicCurve_conductorExponentOdd_of_not_dvd` evaluate the local exponent
  at every odd prime of an actual ABC triple, using exactly the two reduction
  criteria `freyPadicCurve_hasMultiplicativeReduction_iff` and
  `freyPadicCurve_hasGoodReduction_iff` of `FreyOddReduction`.
  `frey_oddConductor_eq_oddRadical` then computes the global odd conductor of
  the rational Frey curve as the odd radical of `a * b * c`.
* **No 2-adic statement.** Every local theorem carries the hypothesis `p ≠ 2`,
  and `oddConductor` deliberately discards the prime `2` from its support.
  No exponent, reduction type or conductor contribution at `2` is defined or
  claimed here.  This mirrors the scope of `FreyOddReduction`, whose file ends
  with the remark that no conductor exponent or classification at `2` is
  asserted.
* **No minimal-model theory.** `conductorExponentOdd` is a function of the
  *given* Weierstrass model: it base-changes `E` to `ℚ_[p]` and reads off the
  reduction type of that particular equation.  It agrees with the arithmetic
  conductor exponent only when the model is minimal at `p` (Mathlib's
  `HasGoodReduction` / `HasMultiplicativeReduction` both extend `IsMinimal`).
  For the Frey curve this minimality is *proved* at every odd prime in
  `FreyOddReduction` (`freyPadicCurve_isMinimal`), so the identification above
  is a statement about the actual conductor.  For an arbitrary model no
  minimality, and hence no conductor claim, is made.
* **No additive reduction, no Tate correction.** In the uncovered case where
  the base change is neither good nor multiplicative, `conductorExponentOdd`
  returns the placeholder constant `2`.  No theorem in this file uses that
  branch; the Ogg–Saito / Tate algorithm and its correction terms (wild
  ramification, additive exponents) are outside the scope of this file.
* The identified object is the **odd radical** of `a * b * c`, not the full
  conductor `N_E` of the Frey curve.

## Design choice

`conductorExponentOdd` takes a curve over `ℚ_[p]` (with `[Fact p.Prime]`), so
that the two local criteria of `FreyOddReduction` apply syntactically without a
base-change step.  The global `oddConductor` performs the base change
`E ↦ E.map (algebraMap ℚ ℚ_[p])` internally.  The two named local theorems
therefore mention `freyPadicCurve p a b` directly, exactly as in
`FreyOddReduction`.
-/

noncomputable section

open scoped BigOperators

namespace LeanFormal.IUT

/-! ## The local odd conductor exponent -/

/-- The odd-prime conductor exponent of a Weierstrass model over `ℚ_[p]`,
read off from its reduction type: `0` for good reduction, `1` for
multiplicative reduction, and the placeholder value `2` otherwise.

Only the first two branches are used (and proved correct for the Frey curve) in
this file; the third branch is not a claim about additive reduction. -/
noncomputable def conductorExponentOdd (p : ℕ) [Fact p.Prime]
    (E : WeierstrassCurve ℚ_[p]) : ℕ := by
  classical
  exact
    if WeierstrassCurve.HasGoodReduction ℤ_[p] E then 0
    else if WeierstrassCurve.HasMultiplicativeReduction ℤ_[p] E then 1
    else 2

/-- Good reduction of the given model contributes local exponent zero. -/
theorem conductorExponentOdd_eq_zero_of_hasGoodReduction
    {p : ℕ} [Fact p.Prime] {E : WeierstrassCurve ℚ_[p]}
    (h : WeierstrassCurve.HasGoodReduction ℤ_[p] E) :
    conductorExponentOdd p E = 0 := by
  classical
  rw [conductorExponentOdd]
  exact if_pos h

/-- Multiplicative reduction of the given model contributes local exponent
one.  The mutual exclusivity of good and multiplicative reduction is Mathlib's
`HasMultiplicativeReduction.not_hasGoodReduction`. -/
theorem conductorExponentOdd_eq_one_of_hasMultiplicativeReduction
    {p : ℕ} [Fact p.Prime] {E : WeierstrassCurve ℚ_[p]}
    (h : WeierstrassCurve.HasMultiplicativeReduction ℤ_[p] E) :
    conductorExponentOdd p E = 1 := by
  classical
  rw [conductorExponentOdd]
  rw [if_neg h.not_hasGoodReduction, if_pos h]

/-! ## The Frey curve at odd primes -/

/-- At an odd prime dividing `a * b * c`, the Frey equation has local odd
conductor exponent one.  This is the "multiplicative" half of the reduction
classification of `FreyOddReduction`. -/
theorem freyPadicCurve_conductorExponentOdd_of_dvd {p a b c : ℕ} [Fact p.Prime]
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    conductorExponentOdd p (freyPadicCurve p a b) = 1 :=
  conductorExponentOdd_eq_one_of_hasMultiplicativeReduction
    ((freyPadicCurve_hasMultiplicativeReduction_iff h hp_two).mpr hdiv)

/-- At an odd prime not dividing `a * b * c`, the Frey equation has local odd
conductor exponent zero.  This is the "good" half of the reduction
classification of `FreyOddReduction`. -/
theorem freyPadicCurve_conductorExponentOdd_of_not_dvd {p a b c : ℕ} [Fact p.Prime]
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hnot : ¬ p ∣ a * b * c) :
    conductorExponentOdd p (freyPadicCurve p a b) = 0 :=
  conductorExponentOdd_eq_zero_of_hasGoodReduction
    ((freyPadicCurve_hasGoodReduction_iff h hp_two).mpr hnot)

/-! ## The global odd conductor -/

/-- The odd part of the arithmetic conductor of a Weierstrass model over `ℚ`:
the finite product of `p ^ conductorExponentOdd p E` over the odd prime
divisors of the rational discriminant of the model.

This is a finite-support definition.  It agrees with the odd part of the
arithmetic conductor when the model is minimal at every odd prime (which is
proved for the Frey curve in `FreyOddReduction`); for a non-minimal model no
such claim is made, and the prime `2` is deliberately excluded. -/
noncomputable def oddConductor (E : WeierstrassCurve ℚ) : ℕ :=
  ∏ p ∈ (E.Δ.num.natAbs.primeFactors ∪ E.Δ.den.primeFactors).filter
      (fun p => p ≠ 2),
    if hp : p.Prime then
      (letI : Fact p.Prime := ⟨hp⟩;
        p ^ conductorExponentOdd p (E.map (algebraMap ℚ ℚ_[p])))
    else 1

/-! ## Base change of the rational Frey curve -/

/-- Base change of the rational Frey curve to `ℚ_[p]` is the `p`-adic Frey
curve used throughout `FreyOddReduction`. -/
theorem rationalFreyWeierstrassCurve_map_eq_freyPadicCurve
    (p a b : ℕ) [Fact p.Prime] :
    (rationalFreyWeierstrassCurve a b).map (algebraMap ℚ ℚ_[p]) =
      freyPadicCurve p a b := by
  simp only [rationalFreyWeierstrassCurve_map, freyPadicCurve]

/-! ## Discriminant and support of the rational Frey curve -/

/-- The actual rational discriminant of the Frey curve, written as the cast of
the natural number `16 * (a * b * c) ^ 2`. -/
theorem rationalFreyWeierstrassCurve_discriminant_natCast_of_isABCTriple
    {a b c : ℕ} (h : IsABCTriple a b c) :
    (rationalFreyWeierstrassCurve a b).Δ = ((16 * (a * b * c) ^ 2 : ℕ) : ℚ) := by
  rw [rationalFreyWeierstrassCurve_discriminant_of_isABCTriple h]
  push_cast
  ring

/-- The odd prime divisors of `16 * (a * b * c) ^ 2` are exactly the odd prime
divisors of `a * b * c`.  The prime `2` is filtered out, so no divisibility
statement about `2` is needed. -/
theorem odd_primeFactors_sixteen_mul_sq {a b c : ℕ} (hne : a * b * c ≠ 0) :
    (16 * (a * b * c) ^ 2).primeFactors.filter (fun p => p ≠ 2) =
      (a * b * c).primeFactors.filter (fun p => p ≠ 2) := by
  have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
  rw [h16, Nat.primeFactors_mul (by positivity) (pow_ne_zero 2 hne),
    Nat.primeFactors_prime_pow (by norm_num : (4 : ℕ) ≠ 0) Nat.prime_two,
    Nat.primeFactors_pow (a * b * c) (by norm_num : (2 : ℕ) ≠ 0)]
  rw [Finset.singleton_union]
  rw [Finset.filter_insert]
  simp

/-! ## The main identification -/

/-- For an actual ABC triple, the odd part of the conductor of the rational
Frey curve is the odd radical of `a * b * c`:
`oddConductor (rationalFreyWeierstrassCurve a b) = ∏_{p ∣ abc, p ≠ 2} p`.

Equivalently, by definition of `abcOddBadPrimeSupport`, the same product can be
written over `abcOddBadPrimeSupport a b c` (see
`frey_oddConductor_eq_oddBadPrimeSupport_prod` below). -/
theorem frey_oddConductor_eq_oddRadical {a b c : ℕ} (h : IsABCTriple a b c) :
    oddConductor (rationalFreyWeierstrassCurve a b) =
      ∏ p ∈ (a * b * c).primeFactors.filter (fun p => p ≠ 2), p := by
  classical
  have hΔ := rationalFreyWeierstrassCurve_discriminant_natCast_of_isABCTriple h
  have hnum : ((16 * (a * b * c) ^ 2 : ℕ) : ℚ).num.natAbs = 16 * (a * b * c) ^ 2 := by
    rw [← Int.cast_natCast, Rat.num_intCast, Int.natAbs_natCast]
  have hden : ((16 * (a * b * c) ^ 2 : ℕ) : ℚ).den = 1 := by
    rw [← Int.cast_natCast, Rat.den_intCast]
  have hsupport :
      ((rationalFreyWeierstrassCurve a b).Δ.num.natAbs.primeFactors ∪
          (rationalFreyWeierstrassCurve a b).Δ.den.primeFactors).filter
            (fun p => p ≠ 2) =
        (a * b * c).primeFactors.filter (fun p => p ≠ 2) := by
    rw [hΔ, hnum, hden, Nat.primeFactors_one, Finset.union_empty]
    exact odd_primeFactors_sixteen_mul_sq (Nat.ne_of_gt h.abcInvariant_product_pos)
  rw [oddConductor, hsupport]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Finset.mem_filter] at hp
  obtain ⟨hp_mem, hp_ne_two⟩ := hp
  rw [Nat.mem_primeFactors] at hp_mem
  obtain ⟨hp_prime, hp_dvd, -⟩ := hp_mem
  letI : Fact p.Prime := ⟨hp_prime⟩
  rw [dif_pos hp_prime]
  have h_exp : conductorExponentOdd p
      ((rationalFreyWeierstrassCurve a b).map (algebraMap ℚ ℚ_[p])) = 1 := by
    rw [rationalFreyWeierstrassCurve_map_eq_freyPadicCurve]
    exact freyPadicCurve_conductorExponentOdd_of_dvd h hp_ne_two hp_dvd
  rw [h_exp, pow_one]

/-- The `abcOddBadPrimeSupport` form of the main identification: the odd
conductor of the rational Frey curve is the product of the odd bad primes of
`a * b * c`. -/
theorem frey_oddConductor_eq_oddBadPrimeSupport_prod {a b c : ℕ}
    (h : IsABCTriple a b c) :
    oddConductor (rationalFreyWeierstrassCurve a b) =
      ∏ p ∈ abcOddBadPrimeSupport a b c, p := by
  simpa only [abcOddBadPrimeSupport] using frey_oddConductor_eq_oddRadical h

end LeanFormal.IUT
