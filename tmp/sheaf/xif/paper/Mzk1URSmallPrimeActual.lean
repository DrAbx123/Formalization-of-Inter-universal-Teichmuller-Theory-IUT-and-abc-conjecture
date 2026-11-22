/- U-C Step (viii) (beta) letter S: actual small-prime set and s^Q (kurt; Lead-approved item ③).

The paper letter log s^Q is the logarithm of an upper bound s^Q of the
small-prime set (IUT IV small-prime definition / Step (vi)-(vii)).  The
repository had logSQ only as an abstract real parameter, so this file provides
the actual objects:

* urSmallPrimeSet X : the primes <= X (the actual small-prime index set);
* urSQ X : an actual upper bound of that set (max 1 of the set);
* ur_prime_le_sQ : prime p <= X implies p <= s^Q X;
* ur_log_prime_le_logSQ : hence log p <= log (s^Q X);
* ur_hlogp_le_logSQ : the packet instantiation for the bad prime p_b, reducing
  the retained condition log p <= logSQ to the paper small-prime membership
  p_b <= X (X is the paper small-prime cutoff, e.g. e*_mod * l).

No sorry, no axiom; only the paper small-prime membership is left as an
explicit hypothesis (provenance: IUT IV small-prime set definition). -/
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual

/-- The actual small-prime index set: the primes up to X. -/
def urSmallPrimeSet (X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter Nat.Prime

/-- The actual upper bound s^Q of the small-prime set (at least 1). -/
def urSQ (X : ℕ) : ℕ :=
  max 1 ((urSmallPrimeSet X).sup id)

/-- The small-prime set is nonempty for X >= 2. -/
theorem urSmallPrimeSet_nonempty {X : ℕ} (hX : 2 ≤ X) : (urSmallPrimeSet X).Nonempty :=
  ⟨2, by
    unfold urSmallPrimeSet
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_Icc.mpr ⟨by omega, hX⟩, Nat.prime_two⟩⟩

/-- A prime at most X belongs to the actual small-prime set. -/
theorem ur_prime_mem_smallPrimeSet {q X : ℕ} (hq : Nat.Prime q) (hqX : q ≤ X) :
    q ∈ urSmallPrimeSet X := by
  unfold urSmallPrimeSet
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_Icc.mpr ⟨hq.one_lt.le, hqX⟩, hq⟩

/-- s^Q is positive. -/
theorem urSQ_pos (X : ℕ) : 0 < urSQ X := by
  unfold urSQ
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

/-- A prime at most X is at most s^Q X (the actual small-prime bound). -/
theorem ur_prime_le_sQ {q X : ℕ} (hq : Nat.Prime q) (hqX : q ≤ X) :
    q ≤ urSQ X := by
  have hmem : q ∈ urSmallPrimeSet X := ur_prime_mem_smallPrimeSet hq hqX
  have hle : q ≤ (urSmallPrimeSet X).sup id := Finset.le_sup (f := id) hmem
  exact le_trans hle (le_max_right _ _)

/-- log monotonicity: a prime at most X has log at most log (s^Q X). -/
theorem ur_log_prime_le_logSQ {q X : ℕ} (hq : Nat.Prime q) (hqX : q ≤ X) :
    Real.log (q : ℝ) ≤ Real.log (urSQ X : ℝ) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  have hle : (q : ℝ) ≤ (urSQ X : ℝ) := by
    exact_mod_cast ur_prime_le_sQ hq hqX
  exact Real.log_le_log hqpos hle

/-- The retained condition log p_b <= logSQ reduces (with logSQ := log (s^Q X))
to the paper small-prime membership p_b <= X. -/
theorem ur_hlogp_le_logSQ {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
    (b : Bad (nativePlaceSelection T)) (X : ℕ)
    (hX : qVFamTensorP T b ≤ X) :
    Real.log (qVFamTensorP T b : ℝ) ≤ Real.log (urSQ X : ℝ) :=
  ur_log_prime_le_logSQ (Fact.out : Nat.Prime (qVFamTensorP T b)) hX

/-- Aggregate bridge (Lead final letter convention): if every bad prime is in
the actual small-prime set (p_b <= X), then the per-b weighted aggregate
sum_b gamma_b * log p_b is at most (sum_b gamma_b) * log (s^Q X).  This makes
BadWeightedLogPBridge (logSQ) provable with logSQ := (sum_b gamma_b) * log
(s^Q X); the only remaining protocol input is the paper small-prime membership
p_b <= X. -/
theorem ur_badWeightedLogP_le {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] (X : ℕ)
    (hX : ∀ b : Bad (nativePlaceSelection T), qVFamTensorP T b ≤ X) :
    (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * Real.log (qVFamTensorP T b : ℝ)) ≤
      (∑ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b) *
        Real.log (urSQ X : ℝ) := by
  have hγnn : ∀ b : Bad (nativePlaceSelection T), 0 ≤ nativeBadLocalWeight T b :=
    fun b => by
      rw [nativeBadLocalWeight_eq_inv (T := T)]
      exact inv_nonneg.mpr (Nat.cast_nonneg _)
  calc (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * Real.log (qVFamTensorP T b : ℝ))
      ≤ ∑ b : Bad (nativePlaceSelection T),
          nativeBadLocalWeight T b * Real.log (urSQ X : ℝ) :=
        Finset.sum_le_sum (fun b _ =>
          mul_le_mul_of_nonneg_left (ur_hlogp_le_logSQ T b X (hX b)) (hγnn b))
    _ = (∑ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b) *
          Real.log (urSQ X : ℝ) := by
        rw [Finset.sum_mul]

#print axioms ur_badWeightedLogP_le

/-- The actual small-prime bound is at most X when X >= 1. -/
theorem urSQ_le {X : ℕ} (hX : 1 ≤ X) : urSQ X ≤ X := by
  unfold urSQ
  refine max_le hX ?_
  refine Finset.sup_le (fun q hq => ?_)
  rw [urSmallPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hq
  exact hq.1.2

/-- Variant with the paper cutoff bound. -/
theorem urSQ_le_of_two_le {X : ℕ} (hX : 2 ≤ X) : urSQ X ≤ X :=
  urSQ_le (le_trans (by norm_num) hX)

#print axioms urSQ_le


/-- Every element of the actual small-prime set is at most X. -/
theorem urSmallPrimeSet_le {X p : ℕ} (hp : p ∈ urSmallPrimeSet X) : p ≤ X := by
  rw [urSmallPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hp
  exact hp.1.2

/-- The actual small-prime set is contained in Icc 1 X. -/
theorem urSmallPrimeSet_subset_Icc (X : ℕ) :
    urSmallPrimeSet X ⊆ Finset.Icc 1 X := by
  intro p hp
  rw [urSmallPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hp
  exact Finset.mem_Icc.mpr hp.1

/-- Every element of the actual small-prime set is prime. -/
theorem urSmallPrimeSet_prime {X p : ℕ} (hp : p ∈ urSmallPrimeSet X) : Nat.Prime p := by
  rw [urSmallPrimeSet, Finset.mem_filter] at hp
  exact hp.2

/-- The product of the actual small primes is positive. -/
theorem urSmallPrimeSet_prod_pos (X : ℕ) :
    0 < ∏ p ∈ urSmallPrimeSet X, p :=
  Finset.prod_pos (fun p hp => (urSmallPrimeSet_prime hp).pos)

/-- Each prime in the set is at most X (divisibility form for prod bounds). -/
theorem urSmallPrimeSet_prod_le (X : ℕ) :
    ∏ p ∈ urSmallPrimeSet X, p ≤ X ^ (urSmallPrimeSet X).card := by
  calc ∏ p ∈ urSmallPrimeSet X, p
      ≤ X ^ (urSmallPrimeSet X).card :=
        Finset.prod_le_pow_card (urSmallPrimeSet X) (fun p => p) X
          (fun p hp => urSmallPrimeSet_le hp)

#print axioms urSmallPrimeSet_le
#print axioms urSmallPrimeSet_prod_pos
#print axioms urSmallPrimeSet_prod_le

#print urSQ
#print ur_prime_le_sQ
#print ur_log_prime_le_logSQ
#print ur_hlogp_le_logSQ

end LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual
end