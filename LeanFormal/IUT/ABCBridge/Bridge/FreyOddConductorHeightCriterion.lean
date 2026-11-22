import LeanFormal.IUT.ABCBridge.Bridge.ABCEllipticHeightCriterion
import LeanFormal.IUT.ABCBridge.Geometry.FreyConductorOdd

/-!
# The odd-conductor denominator criterion for the actual Frey model

This file rewrites the delivered denominator-radical criterion
`ABCFreyJDenominatorHeightCriterion` of
`LeanFormal.IUT.ABCBridge.Bridge.ABCEllipticHeightCriterion` (that file, its
`abcConjecture_iff_freyJDenominatorHeightCriterion`) into a criterion whose
right-hand side is the **odd part of the conductor of the actual Frey model**
`oddConductor (rationalFreyWeierstrassCurve a b)`, delivered in
`LeanFormal.IUT.ABCBridge.Geometry.FreyConductorOdd`.

## Statement of the rewrite

* `ABCInvariantLocalValuations.prime_dvd_product_iff_two_or_dvd_abcJInvariant_den`
  identifies the prime support of `a * b * c` with the prime support of the
  reduced `j`-denominator, up to the prime `2`.
* `IsABCTriple.prime_ne_two_dvd_oddConductor_iff` transfers that identification
  to the actual odd conductor of the Frey model: at every prime `p ≠ 2`,
  `p ∣ oddConductor (rationalFreyWeierstrassCurve a b) ↔ p ∣ (abcJInvariant a b c).den`.
* `IsABCTriple.abcJInvariant_den_radical_eq_twoPow_mul_oddConductor` is the
  numerical bridge: the radical of the reduced denominator differs from the odd
  conductor by at most the single prime `2`,
  `radical (abcJInvariant a b c).den = 2^e * oddConductor (rationalFreyWeierstrassCurve a b)`
  with `e = 1` exactly when `2 ∣ (abcJInvariant a b c).den` (equivalently, by
  `IsABCTriple.two_dvd_abcJInvariant_den_iff`, exactly when
  `5 ≤ padicValNat 2 (a * b * c)`), and `e = 0` otherwise.
* `ABCFreyOddConductorHeightCriterion` is the resulting uniform criterion, and
  `abcConjecture_iff_freyOddConductorHeightCriterion` shows it is equivalent to
  `ABCConjecture` with exactly the same quantifiers and with the additive
  constant shifted by `6 * (1 + epsilon) * Real.log 2` in one direction and
  unchanged in the other.

## Relation to the delivered equivalence chain (constant bookkeeping)

The equivalence chain of `ABCEllipticHeightCriterion` is transported verbatim:

`ABCConjecture ↔ ABCFreyJProductHeightCriterion`
  (`abcConjecture_iff_freyJProductHeightCriterion`), then
`ABCFreyJProductHeightCriterion ↔ ABCFreyJDenominatorHeightCriterion`
  (`freyJProductHeightCriterion_iff_freyJDenominatorHeightCriterion`, which
  already sponsors the `6 * (1 + epsilon) * Real.log 2` shift between the
  product radical and the reduced denominator radical), then the new step
`ABCFreyJDenominatorHeightCriterion ↔ ABCFreyOddConductorHeightCriterion`
  (`freyJDenominatorHeightCriterion_iff_freyOddConductorHeightCriterion`),
which again shifts only by `6 * (1 + epsilon) * Real.log 2`.  The composite is
`abcConjecture_iff_freyOddConductorHeightCriterion`; no step adds a hypothesis
to `ABCConjecture`, weakens a conclusion, or changes the quantifier pattern
`∀ epsilon > 0, ∃ bound, ∀ (a b c), IsABCTriple a b c → ...`.

## Scope boundaries

* **No new ABC strength assumption.** Every statement here is an equivalence
  between already-defined propositions; nothing assumes an IUT estimate, a
  height bound, or any unproved arithmetic input.
* **No `2`-adic statement.** The odd conductor deliberately discards the prime
  `2` (see `FreyConductorOdd`), and the bridge accounts for the discarded
  factor purely as the explicit factor `2^e` above; no statement is made about
  the conductor exponent, reduction type, or arithmetic conductor at `2`.
* **No minimal-model theory.** `oddConductor` is the odd part of the conductor
  of the *given* Weierstrass model; its identification with the odd radical of
  `a * b * c` for actual ABC triples is the delivered
  `frey_oddConductor_eq_oddRadical` of `FreyConductorOdd`, which rests on the
  proved minimality of the Frey equation at odd primes there.  No general
  minimal-model or Ogg–Saito/Tate claim is made here.
* The object identified is the odd radical of `a * b * c`, not the full
  conductor `N_E` of the Frey curve.
-/

noncomputable section

open scoped BigOperators

namespace LeanFormal.IUT

/-! ## Support identification at odd primes -/

/-- For an actual ABC triple and a prime `p`, membership of `p` in the odd bad
prime support of `a * b * c` is exactly divisibility of `p` into the odd
conductor of the rational Frey model.

Both sides are reformulations of "`p` is an odd prime divisor of `a * b * c`":
the left by definition of `abcOddBadPrimeSupport`, the right by
`frey_oddConductor_eq_oddBadPrimeSupport_prod` together with the fact that a
prime divides a product of primes exactly when it is one of them. -/
theorem IsABCTriple.mem_abcOddBadPrimeSupport_iff_dvd_oddConductor {a b c p : ℕ}
    (h : IsABCTriple a b c) [Fact p.Prime] :
    p ∈ abcOddBadPrimeSupport a b c ↔
      p ∣ oddConductor (rationalFreyWeierstrassCurve a b) := by
  have hp : p.Prime := Fact.out
  constructor
  · intro hmem
    rw [frey_oddConductor_eq_oddBadPrimeSupport_prod h]
    exact Finset.dvd_prod_of_mem (fun q => q) hmem
  · intro hdiv
    rw [frey_oddConductor_eq_oddBadPrimeSupport_prod h] at hdiv
    rw [Prime.dvd_finsetProd_iff hp.prime (fun q => q)] at hdiv
    obtain ⟨q, hq, hpq⟩ := hdiv
    have hqprime : q.Prime := (h.mem_abcOddBadPrimeSupport_iff.mp hq).1
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp hpq
    rwa [heq]

/-- Support identification: for an actual ABC triple and a prime `p ≠ 2`,
`p` divides the odd conductor of the rational Frey model exactly when `p`
divides the reduced denominator of the actual `j`-invariant.

This is the composite of `mem_abcOddBadPrimeSupport_iff_dvd_oddConductor` with
`mem_abcOddBadPrimeSupport_iff` and
`IsABCTriple.prime_ne_two_dvd_abcJInvariant_den_iff`
(`ABCInvariantLocalValuations.prime_dvd_product_iff_two_or_dvd_abcJInvariant_den`
with the exceptional prime `2` removed by the hypothesis `p ≠ 2`). -/
theorem IsABCTriple.prime_ne_two_dvd_oddConductor_iff {a b c p : ℕ}
    (h : IsABCTriple a b c) [Fact p.Prime] (hpne : p ≠ 2) :
    p ∣ oddConductor (rationalFreyWeierstrassCurve a b) ↔
      p ∣ (abcJInvariant a b c).den := by
  constructor
  · intro hdiv
    have hmem : p ∈ abcOddBadPrimeSupport a b c :=
      h.mem_abcOddBadPrimeSupport_iff_dvd_oddConductor.mpr hdiv
    exact (h.prime_ne_two_dvd_abcJInvariant_den_iff hpne).mpr
      (h.mem_abcOddBadPrimeSupport_iff.mp hmem).2.2
  · intro hdiv
    exact h.mem_abcOddBadPrimeSupport_iff_dvd_oddConductor.mp
      (h.mem_abcOddBadPrimeSupport_iff.mpr
        ⟨Fact.out, hpne, (h.prime_ne_two_dvd_abcJInvariant_den_iff hpne).mp hdiv⟩)

/-! ## The numerical bridge: the discarded factor is at most `2` -/

/-- The odd prime divisors of the reduced `j`-denominator are exactly the odd
bad primes of `a * b * c`.

The prime `2` is filtered out on the left, so the statement is exactly the
odd part of the support identification of `ABCInvariantRadicalBridge`
(`IsABCTriple.abcJInvariant_den_primeFactors_double`), restated for the
un-doubled denominator. -/
theorem IsABCTriple.abcJInvariant_den_primeFactors_filter_eq_oddBadPrimeSupport
    {a b c : ℕ} (h : IsABCTriple a b c) :
    (abcJInvariant a b c).den.primeFactors.filter (fun p => p ≠ 2) =
      abcOddBadPrimeSupport a b c := by
  classical
  apply Finset.ext
  intro p
  rw [Finset.mem_filter, Nat.mem_primeFactors, h.mem_abcOddBadPrimeSupport_iff]
  constructor
  · rintro ⟨⟨hpprime, hpdiv, -⟩, hpne⟩
    haveI : Fact p.Prime := ⟨hpprime⟩
    exact ⟨hpprime, hpne, (h.prime_ne_two_dvd_abcJInvariant_den_iff hpne).mp hpdiv⟩
  · rintro ⟨hpprime, hpne, hpdiv⟩
    haveI : Fact p.Prime := ⟨hpprime⟩
    exact ⟨⟨hpprime, (h.prime_ne_two_dvd_abcJInvariant_den_iff hpne).mpr hpdiv,
      (abcJInvariant a b c).den_nz⟩, hpne⟩

/-- **Numerical bridge.**  For an actual ABC triple, the radical of the reduced
`j`-denominator equals the odd conductor of the rational Frey model multiplied
by the single explicit factor `2^e`, where `e = 1` exactly when `2` divides the
reduced denominator and `e = 0` otherwise.

Equivalently (see
`abcJInvariant_den_radical_eq_twoPow_mul_oddConductor_padicValNat`), the
condition is `5 ≤ padicValNat 2 (a * b * c)`, so the discarded factor is fully
explicit in the original triple.  No claim about the conductor at `2` is made. -/
theorem IsABCTriple.abcJInvariant_den_radical_eq_twoPow_mul_oddConductor
    {a b c : ℕ} (h : IsABCTriple a b c) :
    natRadical (abcJInvariant a b c).den =
      2 ^ (if 2 ∣ (abcJInvariant a b c).den then 1 else 0) *
        oddConductor (rationalFreyWeierstrassCurve a b) := by
  classical
  have hdenne : (abcJInvariant a b c).den ≠ 0 := (abcJInvariant a b c).den_nz
  have hfilter := h.abcJInvariant_den_primeFactors_filter_eq_oddBadPrimeSupport
  have htwo : ((abcJInvariant a b c).den.primeFactors.filter (fun p => p = 2)).prod
        (fun p => p) =
      2 ^ (if 2 ∣ (abcJInvariant a b c).den then 1 else 0) := by
    rw [Finset.filter_eq']
    by_cases htwo_mem : 2 ∈ (abcJInvariant a b c).den.primeFactors
    · have htwo_dvd : 2 ∣ (abcJInvariant a b c).den :=
        (Nat.mem_primeFactors.mp htwo_mem).2.1
      rw [if_pos htwo_mem, Finset.prod_singleton, if_pos htwo_dvd]
      norm_num
    · have htwo_not_dvd : ¬ 2 ∣ (abcJInvariant a b c).den := fun hdiv =>
        htwo_mem (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hdiv, hdenne⟩)
      rw [if_neg htwo_mem, Finset.prod_empty, if_neg htwo_not_dvd]
      norm_num
  calc natRadical (abcJInvariant a b c).den
      = (abcJInvariant a b c).den.primeFactors.prod (fun p => p) :=
        natRadical_eq_prod_primeFactors _
    _ = ((abcJInvariant a b c).den.primeFactors.filter (fun p => p = 2)).prod
            (fun p => p) *
          ((abcJInvariant a b c).den.primeFactors.filter (fun p => p ≠ 2)).prod
            (fun p => p) :=
        (Finset.prod_filter_mul_prod_filter_not _ (fun p => p = 2) (fun p => p)).symm
    _ = 2 ^ (if 2 ∣ (abcJInvariant a b c).den then 1 else 0) *
          oddConductor (rationalFreyWeierstrassCurve a b) := by
        rw [htwo, hfilter, ← frey_oddConductor_eq_oddBadPrimeSupport_prod h]

/-- The same numerical bridge with the discarded factor made explicit in the
original ABC triple: the exponent `e ∈ {0,1}` is `1` exactly when
`5 ≤ padicValNat 2 (a * b * c)`. -/
theorem IsABCTriple.abcJInvariant_den_radical_eq_twoPow_mul_oddConductor_padicValNat
    {a b c : ℕ} (h : IsABCTriple a b c) :
    natRadical (abcJInvariant a b c).den =
      2 ^ (if 5 ≤ padicValNat 2 (a * b * c) then 1 else 0) *
        oddConductor (rationalFreyWeierstrassCurve a b) := by
  rw [h.abcJInvariant_den_radical_eq_twoPow_mul_oddConductor]
  simp only [h.two_dvd_abcJInvariant_den_iff]

/-- The odd conductor of the rational Frey model of an actual ABC triple is
nonzero.  This follows from the numerical bridge and the positivity of the
radical of the reduced denominator. -/
theorem IsABCTriple.oddConductor_ne_zero {a b c : ℕ} (h : IsABCTriple a b c) :
    oddConductor (rationalFreyWeierstrassCurve a b) ≠ 0 := by
  intro hzero
  have hrad := h.abcJInvariant_den_radical_eq_twoPow_mul_oddConductor
  rw [hzero, mul_zero] at hrad
  exact absurd hrad (ne_of_gt (natRadical_pos (abcJInvariant a b c).den))

/-! ## The logarithmic form of the bridge -/

/-- Exact logarithmic form of the numerical bridge: replacing the radical of
the reduced `j`-denominator by the odd conductor of the rational Frey model
changes the logarithm by exactly the discarded factor, i.e. by `Real.log 2`
when `2` divides the reduced denominator and by `0` otherwise. -/
theorem IsABCTriple.abcJInvariant_den_logRadical_eq_oddConductor_add_log
    {a b c : ℕ} (h : IsABCTriple a b c) :
    Real.log (radical (abcJInvariant a b c).den : ℝ) =
      Real.log (oddConductor (rationalFreyWeierstrassCurve a b) : ℝ) +
        (if 2 ∣ (abcJInvariant a b c).den then Real.log 2 else 0) := by
  classical
  have hrad := h.abcJInvariant_den_radical_eq_twoPow_mul_oddConductor
  have hoddne : oddConductor (rationalFreyWeierstrassCurve a b) ≠ 0 :=
    h.oddConductor_ne_zero
  by_cases htwo : 2 ∣ (abcJInvariant a b c).den
  · have hvalue : radical (abcJInvariant a b c).den =
        2 * oddConductor (rationalFreyWeierstrassCurve a b) := by
      change natRadical (abcJInvariant a b c).den =
        2 * oddConductor (rationalFreyWeierstrassCurve a b)
      rw [hrad, if_pos htwo, pow_one]
    rw [hvalue, if_pos htwo]
    push_cast
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by exact_mod_cast hoddne)]
    ring
  · have hvalue : radical (abcJInvariant a b c).den =
        oddConductor (rationalFreyWeierstrassCurve a b) := by
      change natRadical (abcJInvariant a b c).den =
        oddConductor (rationalFreyWeierstrassCurve a b)
      rw [hrad, if_neg htwo, pow_zero, one_mul]
    rw [hvalue, if_neg htwo, add_zero]

/-- Upper logarithmic bound: the radical of the reduced `j`-denominator exceeds
the odd conductor of the rational Frey model by at most the factor `2`, hence by
at most `Real.log 2` in the logarithm.

This is the inequality used in the forward direction of the criterion
rewrite. -/
theorem IsABCTriple.abcJInvariant_den_logRadical_le_oddConductor_add_log_two
    {a b c : ℕ} (h : IsABCTriple a b c) :
    Real.log (radical (abcJInvariant a b c).den : ℝ) ≤
      Real.log (oddConductor (rationalFreyWeierstrassCurve a b) : ℝ) + Real.log 2 := by
  rw [h.abcJInvariant_den_logRadical_eq_oddConductor_add_log]
  by_cases htwo : 2 ∣ (abcJInvariant a b c).den
  · rw [if_pos htwo]
  · rw [if_neg htwo]
    have hlogtwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith

/-- Lower logarithmic bound: the odd conductor of the rational Frey model is at
most the radical of the reduced `j`-denominator.

This is the inequality used in the reverse direction of the criterion
rewrite. -/
theorem IsABCTriple.abcJInvariant_den_oddConductor_logRadical_le
    {a b c : ℕ} (h : IsABCTriple a b c) :
    Real.log (oddConductor (rationalFreyWeierstrassCurve a b) : ℝ) ≤
      Real.log (radical (abcJInvariant a b c).den : ℝ) := by
  rw [h.abcJInvariant_den_logRadical_eq_oddConductor_add_log]
  by_cases htwo : 2 ∣ (abcJInvariant a b c).den
  · rw [if_pos htwo]
    have hlogtwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  · rw [if_neg htwo, add_zero]

/-! ## The odd-conductor criterion -/

/-- The uniform `j`-height criterion for the actual Frey model, with the
right-hand side measured by the odd part of the conductor of that model instead
of by the radical of the reduced `j`-denominator.

The quantifier pattern is the one of
`ABCFreyJDenominatorHeightCriterion` (and of `ABCConjecture`): for every
positive real `epsilon` there is one real constant that works for every
positive primitive ABC triple.  The two criteria differ only by the explicit
`Real.log 2` bookkeeping of the numerical bridge. -/
def ABCFreyOddConductorHeightCriterion : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ bound : ℝ,
    ∀ (a b c : ℕ) (h : IsABCTriple a b c),
      letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
      Height.logHeight₁ (rationalFreyWeierstrassCurve a b).j ≤
        6 * (1 + epsilon) *
          Real.log (oddConductor (rationalFreyWeierstrassCurve a b) : ℝ) + bound

/-- Replacing the radical of the reduced `j`-denominator by the odd conductor of
the rational Frey model changes the uniform constant by at most
`6 * (1 + epsilon) * Real.log 2`.  The reverse implication keeps the constant
unchanged.  The coefficient `6 * (1 + epsilon)` is nonnegative because the
quantifier retains the hypothesis `0 < epsilon`. -/
theorem freyJDenominatorHeightCriterion_iff_freyOddConductorHeightCriterion :
    ABCFreyJDenominatorHeightCriterion ↔ ABCFreyOddConductorHeightCriterion := by
  constructor
  · intro hdenominator epsilon hepsilon
    obtain ⟨bound, hbound⟩ := hdenominator epsilon hepsilon
    refine ⟨bound + 6 * (1 + epsilon) * Real.log 2, ?_⟩
    intro a b c h
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    have hcoefficient : 0 ≤ 6 * (1 + epsilon) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left
      h.abcJInvariant_den_logRadical_le_oddConductor_add_log_two hcoefficient
    calc
      Height.logHeight₁ (rationalFreyWeierstrassCurve a b).j ≤
          6 * (1 + epsilon) * Real.log (radical (abcJInvariant a b c).den : ℝ) +
            bound :=
        hbound a b c h
      _ ≤ 6 * (1 + epsilon) *
            (Real.log (oddConductor (rationalFreyWeierstrassCurve a b) : ℝ) +
              Real.log 2) + bound :=
        add_le_add_left hscaled bound
      _ = 6 * (1 + epsilon) *
            Real.log (oddConductor (rationalFreyWeierstrassCurve a b) : ℝ) +
              (bound + 6 * (1 + epsilon) * Real.log 2) := by ring
  · intro hoddConductor epsilon hepsilon
    obtain ⟨bound, hbound⟩ := hoddConductor epsilon hepsilon
    refine ⟨bound, ?_⟩
    intro a b c h
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    have hcoefficient : 0 ≤ 6 * (1 + epsilon) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left
      h.abcJInvariant_den_oddConductor_logRadical_le hcoefficient
    exact (hbound a b c h).trans (add_le_add_left hscaled bound)

/-- The product-radical criterion of `ABCEllipticHeightCriterion` is equivalent
to the odd-conductor criterion of this file, so the odd-conductor criterion is
not a weakening of the delivered chain: it is exactly as strong as
`ABCFreyJProductHeightCriterion` (and hence as `ABCConjecture`). -/
theorem freyJProductHeightCriterion_iff_freyOddConductorHeightCriterion :
    ABCFreyJProductHeightCriterion ↔ ABCFreyOddConductorHeightCriterion :=
  freyJProductHeightCriterion_iff_freyJDenominatorHeightCriterion.trans
    freyJDenominatorHeightCriterion_iff_freyOddConductorHeightCriterion

/-- The actual ABC conjecture is equivalent to the uniform canonical `j`-height
estimate for the actual rational Frey model with the odd conductor
`oddConductor (rationalFreyWeierstrassCurve a b)` on the right.

This is the "conductor form" of the delivered equivalence chain: the right-hand
side is the odd part of the conductor of the actual Frey model, and the constant
bookkeeping is `6 * (1 + epsilon) * Real.log 2` for each of the two radical
rewrites.  The equivalence adds no hypothesis to `ABCConjecture` and does not
assume any IUT estimate; it only rewrites the already-defined criterion. -/
theorem abcConjecture_iff_freyOddConductorHeightCriterion :
    ABCConjecture ↔ ABCFreyOddConductorHeightCriterion :=
  abcConjecture_iff_freyJDenominatorHeightCriterion.trans
    freyJDenominatorHeightCriterion_iff_freyOddConductorHeightCriterion

end LeanFormal.IUT
