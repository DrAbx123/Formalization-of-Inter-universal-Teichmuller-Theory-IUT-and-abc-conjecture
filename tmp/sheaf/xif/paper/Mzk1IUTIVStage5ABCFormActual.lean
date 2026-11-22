import LeanFormal.IUT.ABCBridge.Statement
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1IUTIVStage5ABCFormActual — Stage 5 on the ABC rational points

Specializes the dependency-free Stage-5 numerical absorption to the ABC
rational-point height and arithmetic weight.  The two literal estimates are
explicit hypotheses; the output is the ABC-form additive height bound.
No closure claim; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual

open LeanFormal.IUT

/-- ABC-form additive height bound on the rational points. -/
def ABCFormAdditiveHeightBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A : ℝ,
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + ε) * arithmeticWeight (abcRationalPoint a c) + A

/-- Stage 5 with the ABC dictionary: from the literal height comparison and the
main log-volume estimate on ABC triples one gets the ABC-form additive bound. -/
theorem exists_delta_sq_le_one_add {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ (1 + δ) ^ 2 ≤ 1 + ε := by
  refine ⟨min (ε / 4) (1 / 2), ?_, ?_⟩
  · exact lt_min (by positivity) (by norm_num)
  · have hδ0 : 0 < min (ε / 4) (1 / 2) := lt_min (by positivity) (by norm_num)
    have hδle : min (ε / 4) (1 / 2) ≤ ε / 4 := min_le_left _ _
    have hδhalf : min (ε / 4) (1 / 2) ≤ 1 / 2 := min_le_right _ _
    have hδsq : (min (ε / 4) (1 / 2)) ^ 2 ≤
        (min (ε / 4) (1 / 2)) * (1 / 2) := by
      simpa [pow_two] using mul_le_mul_of_nonneg_left hδhalf hδ0.le
    nlinarith [hδle, hδsq, hε.le]

theorem arithmeticWeight_nonneg_local (x : Rat) : 0 ≤ arithmeticWeight x := by
  unfold arithmeticWeight
  refine Finset.sum_nonneg fun p hp => Real.log_nonneg ?_
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
    · exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
  · exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le

theorem abcFormAdditiveHeightBound_of_literalEstimates
    (logVolume : Nat → Nat → Nat → ℝ) (hullVolume : ℝ)
    (hheight : ∀ δ : ℝ, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c)
    (hmain : ∀ δ : ℝ, 0 < δ → ∃ D : ℝ,
      ∀ a b c : Nat, IsABCTriple a b c →
        logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
          hullVolume + D) :
    ABCFormAdditiveHeightBound := by
  intro ε hε
  obtain ⟨δ, hδ0, hδsq⟩ := exists_delta_sq_le_one_add hε
  obtain ⟨D, hD⟩ := hmain δ hδ0
  refine ⟨(1 + δ) * (hullVolume + D), fun a b c habc => ?_⟩
  have h1 := hheight δ hδ0 a b c habc
  have h2 := hD a b c habc
  have hδnonneg : 0 ≤ 1 + δ := by linarith
  have hmul := mul_le_mul_of_nonneg_left h2 hδnonneg
  have hchain : Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + δ) * ((1 + δ) * arithmeticWeight (abcRationalPoint a c) +
        hullVolume + D) :=
    le_trans h1 hmul
  have hw : 0 ≤ arithmeticWeight (abcRationalPoint a c) :=
    arithmeticWeight_nonneg_local _
  have hcoef : (1 + δ) * ((1 + δ) * arithmeticWeight (abcRationalPoint a c) +
        hullVolume + D) =
      (1 + δ) ^ 2 * arithmeticWeight (abcRationalPoint a c) +
        (1 + δ) * (hullVolume + D) := by
    ring
  rw [hcoef] at hchain
  have hsqmul : (1 + δ) ^ 2 * arithmeticWeight (abcRationalPoint a c) ≤
      (1 + ε) * arithmeticWeight (abcRationalPoint a c) :=
    mul_le_mul_of_nonneg_right hδsq hw
  linarith

/-- ABCConjecture from the ABC-form additive height bound (core contract equivalence). -/
theorem abcConjecture_of_abcFormAdditiveHeightBound
    (h : ABCFormAdditiveHeightBound) : ABCConjecture :=
  abcConjecture_iff_abcArithmeticWeightHeightBound.mpr h

/-- The Stage-5 rung: literal height/main estimates imply ABC. -/
theorem abcConjecture_of_literalEstimates
    (logVolume : Nat → Nat → Nat → ℝ) (hullVolume : ℝ)
    (hheight : ∀ δ : ℝ, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c)
    (hmain : ∀ δ : ℝ, 0 < δ → ∃ D : ℝ,
      ∀ a b c : Nat, IsABCTriple a b c →
        logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
          hullVolume + D) :
    ABCConjecture :=
  abcConjecture_of_abcFormAdditiveHeightBound
    (abcFormAdditiveHeightBound_of_literalEstimates logVolume hullVolume hheight hmain)


/-- Non-dilated-main variant of the ABС-form Stage-5 rung. -/
theorem abcFormAdditiveHeightBound_of_literalEstimates_nondilatedMain
    (logVolume : Nat → Nat → Nat → ℝ) (hullVolume : ℝ)
    (hheight : ∀ δ : ℝ, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c)
    (hmain : ∃ D : ℝ, ∀ a b c : Nat, IsABCTriple a b c →
      logVolume a b c ≤ arithmeticWeight (abcRationalPoint a c) + hullVolume + D) :
    ABCFormAdditiveHeightBound := by
  intro ε hε
  obtain ⟨D, hD⟩ := hmain
  refine ⟨(1 + ε) * (hullVolume + D), fun a b c habc => ?_⟩
  have h1 := hheight ε hε a b c habc
  have h2 := hD a b c habc
  have hεnonneg : 0 ≤ 1 + ε := by linarith
  have hmul := mul_le_mul_of_nonneg_left h2 hεnonneg
  have hchain : Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + ε) * (arithmeticWeight (abcRationalPoint a c) + hullVolume + D) :=
    le_trans h1 hmul
  have hcoef : (1 + ε) * (arithmeticWeight (abcRationalPoint a c) + hullVolume + D) =
      (1 + ε) * arithmeticWeight (abcRationalPoint a c) +
        (1 + ε) * (hullVolume + D) := by
    ring
  rw [hcoef] at hchain
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual

end
