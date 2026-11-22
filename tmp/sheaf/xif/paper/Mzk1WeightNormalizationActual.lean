/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # A703 hull: normalized arithmetic weight (triple-dependent, no `hfull`)

After A703 the comparison object is triple-dependent: the bad primes are the
prime factors of `a*b*c`, and the local degree coefficient `[F_v : Q_p]` must be
normalized by the global degree `[F : Q]`.  This file records that normalization:

* `normalizedWeight n = Σ_{p | n} log p = log (natRadical n)`;
* `tripleNormalizedWeight a b c = Σ_{p | a*b*c} log p`, and for an ABC triple it
  equals `arithmeticWeight (abcRationalPoint a c)`;
* **local degree normalization** (abstract, the actual content): for the complete
  set of places `v | p` the normalized degrees `d_v / D` (`D = Σ_v d_v`) satisfy
  `Σ_v (d_v / D) · (v_p(·) · log p) = v_p(·) · log p` — the coefficient `d_v`
  disappears, so the `d_b` obstruction of the old `N`-scaling is gone;
* specialization `d_v = 1` (the `F = Q` model): `Σ_v (1/#ι) · (v₀ log p) = v₀ log p`.

No `hfull`, no `N = a+b+c+1` scaling, no canonical object changed;
ABC gate NOT passed.  Old `final_conditional_ABC` chain is RETRACTED/VACUOUS
(see mainline `Mzk1FinalConditionalVacuityActual`). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1WeightNormalizationActual

open LeanFormal.IUT
open scoped BigOperators

/-- Normalized arithmetic weight of `n`: sum of `log p` over the prime factors. -/
def normalizedWeight (n : Nat) : Real :=
  ∑ p ∈ n.primeFactors, Real.log (p : Real)

theorem normalizedWeight_eq_log_natRadical (n : Nat) :
    normalizedWeight n = Real.log (natRadical n : Real) :=
  (natRadical_cast_log_eq_sum_primeFactors n).symm

/-- Triple-dependent bad prime set: the prime factors of `a*b*c` (NOT an `N`-scaling). -/
def tripleBadPrimes (a b c : Nat) : Finset Nat :=
  (a * b * c).primeFactors

/-- Triple-dependent normalized weight `Σ_{p | abc} log p`. -/
def tripleNormalizedWeight (a b c : Nat) : Real :=
  ∑ p ∈ tripleBadPrimes a b c, Real.log (p : Real)

theorem tripleNormalizedWeight_eq_radical (a b c : Nat) :
    tripleNormalizedWeight a b c = Real.log (natRadical (a * b * c) : Real) := by
  rw [tripleNormalizedWeight, tripleBadPrimes]
  exact (natRadical_cast_log_eq_sum_primeFactors (a * b * c)).symm

/-- For an ABC triple, the triple-dependent normalized weight is the arithmetic weight. -/
theorem tripleNormalizedWeight_abcWeight {a b c : Nat} (h : IsABCTriple a b c) :
    tripleNormalizedWeight a b c = arithmeticWeight (abcRationalPoint a c) := by
  rw [tripleNormalizedWeight_eq_radical]
  exact (arithmeticWeight_abcRationalPoint h).symm

/-! ## Local degree normalization (the actual `d_v`-coefficient cancellation) -/

/-- **Degree-normalized local sum**: if the local valuations are all the same rational
valuation `v₀` (all places over `p`), then
`Σ_v (d_v / D) · (v_v · log p) = v₀ · log p`, where `D = Σ_v d_v`.
The normalized degrees sum to `1`, so the `d_v` coefficient disappears. -/
theorem local_degree_normalized_sum {ι : Type*} [Fintype ι]
    (p : Nat) (D : Real) (d v : ι → Real) (v₀ : Real) (hD : D ≠ 0)
    (hsum : ∑ i, d i = D) (hconst : ∀ i, v i = v₀) :
    (∑ i, (d i / D) * (v i * Real.log (p : Real))) =
      v₀ * Real.log (p : Real) := by
  have hstep : (∑ i, (d i / D) * (v i * Real.log (p : Real))) =
      (∑ i, d i / D) * (v₀ * Real.log (p : Real)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [hconst i]
  rw [hstep, ← Finset.sum_div, hsum, div_self hD, one_mul]

/-- `F = Q` (all local degrees `d_v = 1`) specialization: `D = #ι` and the
normalized local sum is just `v₀ log p`; no degree coefficient remains. -/
theorem local_degree_normalized_sum_card {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : Nat) (v₀ : Real) (v : ι → Real) (hv : ∀ i, v i = v₀) :
    (∑ i, ((1 : Real) / (Fintype.card ι : Real)) * (v i * Real.log (p : Real))) =
      v₀ * Real.log (p : Real) := by
  have hD : (Fintype.card ι : Real) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum : (∑ _i : ι, (1 : Real)) = (Fintype.card ι : Real) := by
    simp [Finset.sum_const, Finset.card_univ]
  have hmain := local_degree_normalized_sum (ι := ι) p (Fintype.card ι : Real)
    (fun _ => (1 : Real)) v v₀ hD hsum hv
  simpa using hmain

def weightNormalizationRows : List (String × String × String) :=
  [ ("normalizedWeight", "normalizedWeight n = Σ_{p|n} log p", "DEF"),
    ("radical dictionary", "normalizedWeight_eq_log_natRadical", "PROVED"),
    ("triple-dependent bad primes", "tripleBadPrimes a b c = (a*b*c).primeFactors", "DEF (no hfull)"),
    ("triple normalized weight", "tripleNormalizedWeight_abcWeight", "PROVED (ABC triple)"),
    ("local degree normalization", "local_degree_normalized_sum", "PROVED (d_v/D sums to 1)"),
    ("F = Q specialization", "local_degree_normalized_sum_card", "PROVED"),
    ("scope", "no hfull/N-scaling; old chain RETRACTED; ABC gate NOT passed", "INTEGRITY") ]

theorem weightNormalizationRows_length : weightNormalizationRows.length = 7 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1WeightNormalizationActual.normalizedWeight_eq_log_natRadical
#print axioms LeanFormal.IUT.XiFPaper.Mzk1WeightNormalizationActual.tripleNormalizedWeight_abcWeight
#print axioms LeanFormal.IUT.XiFPaper.Mzk1WeightNormalizationActual.local_degree_normalized_sum
#print axioms LeanFormal.IUT.XiFPaper.Mzk1WeightNormalizationActual.local_degree_normalized_sum_card

end LeanFormal.IUT.XiFPaper.Mzk1WeightNormalizationActual

end