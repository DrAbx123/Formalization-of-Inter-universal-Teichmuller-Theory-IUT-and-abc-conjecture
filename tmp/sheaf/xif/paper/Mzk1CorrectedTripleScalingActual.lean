/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PaperComparisonRegionScalingActual
import tmp.sheaf.xif.paper.Mzk1LanaBridgeAuditActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-!
# A655 CORRECTED triple scaling (bad-support form; mainline, design only)

The hull scaling formula is expected to involve only the **bad-support part** of
`N = a + b + c + 1` (the primes of `N` at bad places), not all of `N`.  This file
therefore parameterizes the formula by `badPart : Nat -> Nat` (intended:
`∏_{p ∈ bad} p^{v_p(N)}`) and states:

* `CorrectedRegionFormula point badPart const`: the uncorrected log-volume is the unit
  region's plus `log (badPart N)` plus `const` (NOT proved; expected from hull);
* `corrected_gap1_reduction`: under the formula, Gap 1 is equivalent to the pure
  arithmetic inequality `log c <= (1+ε)*(unit + log (badPart N) + const)`;
* `corrected_gap1_fails_of_bounded_badPart`: if the bad support is too small
  (`badPart` bounded by `K >= 1`), then for every `ε > 0` the corrected region FAILS
  Gap 1 on large triples of the family `(1, n, n+1)` (height `log (n+1)` grows
  unboundedly while the region bound stays bounded).

Nothing canonical is changed; formula remains a named hypothesis.  ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1CorrectedTripleScalingActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open Mzk1LanaBridgeAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Inverse triple-dependent scaling (p-adic contraction direction). -/
noncomputable def tripleScaleInv (a b c : Nat) : S1902Carrier T → S1902Carrier T :=
  fun x v => (((a + b + c + 1 : ℕ) : ℚ_[(qVFamTensorP T v)])⁻¹) • x v

/-- The corrected paper comparison region. -/
noncomputable def correctedPaperComparisonRegion
    (point : Nat → Nat → Nat → S1902Carrier T) (a b c : Nat) : Set (S1902Carrier T) :=
  tripleScaleInv T a b c '' (s1902UnitRegion T ∪ {point a b c})

/-- **Refined formula hypothesis** (not proved): the corrected region's real log-volume
  is the unit region's plus `log (badPart (a+b+c+1))` plus `const`.  Intended
  `badPart N = ∏_{p ∈ bad} p^{v_p(N)}`; the formula involves only the bad support. -/
def CorrectedRegionFormula (point : Nat → Nat → Nat → S1902Carrier T)
    (badPart : Nat → Nat) (const : ℝ) : Prop :=
  ∀ a b c : Nat,
    (s1902LogVolume T (correctedPaperComparisonRegion T point a b c)).toReal =
      (s1902LogVolume T (s1902UnitRegion T)).toReal +
        Real.log (((badPart (a + b + c + 1) : ℕ)) : ℝ) + const

/-- **Reduction form**: under the refined formula, Gap 1 is exactly the arithmetic
  inequality `log c <= (1+ε)*(unit + log (badPart N) + const)`. -/
theorem corrected_gap1_reduction
    (point : Nat → Nat → Nat → S1902Carrier T) (badPart : Nat → Nat) (const : ℝ)
    (hformula : CorrectedRegionFormula T point badPart const) (ε : ℝ) (hε : 0 < ε)
    (harith : ∀ a b c : Nat, IsABCTriple a b c →
      Real.log (c : ℝ) ≤
        (1 + ε) * ((s1902LogVolume T (s1902UnitRegion T)).toReal +
          Real.log (((badPart (a + b + c + 1) : ℕ)) : ℝ) + const)) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + ε) *
          (s1902LogVolume T (correctedPaperComparisonRegion T point a b c)).toReal := by
  intro a b c habc
  rw [hformula a b c]
  rw [show Height.logHeight₁ (abcRationalPoint a c) = Real.log (c : ℝ) from
    abcRationalPoint_logHeight₁ habc]
  exact harith a b c habc

/-- **Counterexample boundary**: if the bad support is bounded (`badPart N <= K`, with
  `K >= 1`), then the corrected region fails Gap 1 for large triples of the family
  `(1, n, n+1)` (height grows like `log n` while the region bound is bounded). -/
theorem corrected_gap1_fails_of_bounded_badPart
    (point : Nat → Nat → Nat → S1902Carrier T) (badPart : Nat → Nat)
    (const K : ℝ) (hK : 1 ≤ K)
    (hbounded : ∀ N : Nat, ((badPart N : ℕ) : ℝ) ≤ K)
    (hformula : CorrectedRegionFormula T point badPart const)
    (ε : ℝ) (hε : 0 < ε) :
    ¬ (∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + ε) *
            (s1902LogVolume T (correctedPaperComparisonRegion T point a b c)).toReal) := by
  intro h
  set M : ℝ := (s1902LogVolume T (s1902UnitRegion T)).toReal with hM
  set B : ℝ := (1 + ε) * (M + Real.log K + const) with hB
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp (max B 0))
  have hnpos : 0 < n := by
    have : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (Real.exp_pos _) (le_of_lt hn)
    exact_mod_cast this
  have h1n : 1 ≤ n := hnpos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hlog_gt : B < Real.log ((n : ℝ)) := by
    have h1 : Real.log (Real.exp (max B 0)) = max B 0 := Real.log_exp _
    have h2 : Real.log (Real.exp (max B 0)) < Real.log ((n : ℝ)) := by
      apply Real.log_lt_log (Real.exp_pos _) hn
    rw [h1] at h2
    exact lt_of_le_of_lt (le_max_left _ _) h2
  have hlog_n1 : B < Real.log (((n + 1 : ℕ)) : ℝ) := by
    have hle : Real.log ((n : ℝ)) ≤ Real.log (((n + 1 : ℕ)) : ℝ) := by
      apply Real.log_le_log hnR
      exact_mod_cast Nat.le_succ n
    linarith
  -- the triple (1, n, n+1)
  have htriple : IsABCTriple 1 n (n + 1) :=
    ⟨Nat.one_pos, hnpos, Nat.add_comm 1 n, Nat.coprime_one_left n⟩
  have hbound := h 1 n (n + 1) htriple
  rw [show Height.logHeight₁ (abcRationalPoint 1 (n + 1)) = Real.log ((n + 1 : ℕ) : ℝ) from
    abcRationalPoint_logHeight₁ htriple] at hbound
  rw [hformula 1 n (n + 1)] at hbound
  have hN : 1 + n + (n + 1) + 1 = 2 * n + 3 := by ring
  rw [hN] at hbound
  have hlogbad : Real.log (((badPart (2 * n + 3) : ℕ)) : ℝ) ≤ Real.log K := by
    by_cases hzero : badPart (2 * n + 3) = 0
    · rw [hzero]
      simp only [Nat.cast_zero]
      rw [Real.log_zero]
      exact Real.log_nonneg (by linarith : (1 : ℝ) ≤ K)
    · have hpos : (0 : ℝ) < ((badPart (2 * n + 3) : ℕ) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hzero
      exact Real.log_le_log hpos (hbounded (2 * n + 3))
  have hRHS_le : (1 + ε) * (M + Real.log (((badPart (2 * n + 3) : ℕ)) : ℝ) + const) ≤ B := by
    have hcoef : (0 : ℝ) < 1 + ε := by linarith
    have hinner : M + Real.log (((badPart (2 * n + 3) : ℕ)) : ℝ) + const ≤ M + Real.log K + const := by
      linarith
    calc (1 + ε) * (M + Real.log (((badPart (2 * n + 3) : ℕ)) : ℝ) + const)
        ≤ (1 + ε) * (M + Real.log K + const) := by
          exact mul_le_mul_of_nonneg_left hinner hcoef.le
      _ = B := by rfl
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1CorrectedTripleScalingActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1CorrectedTripleScalingActual.corrected_gap1_reduction
#print axioms LeanFormal.IUT.XiFPaper.Mzk1CorrectedTripleScalingActual.corrected_gap1_fails_of_bounded_badPart