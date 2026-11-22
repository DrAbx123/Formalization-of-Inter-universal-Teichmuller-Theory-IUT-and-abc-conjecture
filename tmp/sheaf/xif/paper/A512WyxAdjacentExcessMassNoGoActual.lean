/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
/- Ported for reuse from https://github.com/wyx66624/ABCConjecture (Apache-2.0; author: ChatGPT),
   files Lean/IUTThreeClosures/ABCStatement.lean and ABCCounterexampleExcessMassGate.lean.
   Only the fully retrieved, self-contained definitions and lemmas are ported; the
   main no-go gate theorem is not included because the source fetch was truncated.
   No unconditional abc claim is made. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic

namespace IUTThreeClosures

open scoped BigOperators

/-- Product of the distinct prime divisors (inlined from `ABCStatement.lean`). -/
def abcRadical (n : Nat) : Nat := Finset.prod n.primeFactors id

/-- Pairwise coprimality of an abc triple (inlined). -/
def PairwiseCoprimeABC (a b c : Nat) : Prop :=
  Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime c a

/-- The standard logarithmic form of the abc conjecture (inlined). -/
def ABCConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, ∀ a b c : Nat,
      0 < a → 0 < b → 0 < c →
      a + b = c → PairwiseCoprimeABC a b c →
      Real.log (((max a (max b c) : Nat) : ℝ)) ≤ 
        (1 + ε) * Real.log (((abcRadical (a * b * c) : Nat) : ℝ)) + C

noncomputable section

/-- Logarithmic height of the adjacent triple `(1,b,b+1)` (source definition). -/
def adjacentABCHeight (b : Nat) : ℝ := Real.log ((b + 1 : Nat) : ℝ)

/-- Logarithmic radical mass of the adjacent triple `(1,b,b+1)` (source definition). -/
def adjacentABCRadicalLog (b : Nat) : ℝ := 
  Real.log ((abcRadical (b * (b + 1)) : Nat) : ℝ)

/-- Logarithmic mass lost when passing to the radical (source definition). -/
def adjacentABCExcessMass (b : Nat) : ℝ := 
  Real.log ((b * (b + 1) : Nat) : ℝ) - adjacentABCRadicalLog b

/-- The product of two adjacent positive integers has logarithm at most twice the
logarithmic height of the corresponding abc triple (ported theorem). -/
theorem adjacentABC_log_product_le_two_height (b : Nat) (hb : 0 < b) :
    Real.log ((b * (b + 1) : Nat) : ℝ) ≤ 2 * adjacentABCHeight b := by
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hbpR : 0 < ((b + 1 : Nat) : ℝ) := by exact_mod_cast Nat.succ_pos b
  have hleR : (b : ℝ) ≤ ((b + 1 : Nat) : ℝ) := by
    exact_mod_cast (Nat.le_succ b)
  have hlog : Real.log (b : ℝ) ≤ Real.log ((b + 1 : Nat) : ℝ) := 
    Real.log_le_log hbR hleR
  rw [adjacentABCHeight, Nat.cast_mul, Real.log_mul hbR.ne' hbpR.ne']
  calc Real.log (b : ℝ) + Real.log ((b + 1 : Nat) : ℝ)
      ≤ Real.log ((b + 1 : Nat) : ℝ) + Real.log ((b + 1 : Nat) : ℝ) := add_le_add_right hlog _
    _ = 2 * Real.log ((b + 1 : Nat) : ℝ) := by rw [two_mul]

/-- The adjacent triple `(1,b,b+1)` is primitive (ported theorem). -/
theorem one_adjacent_pairwiseCoprimeABC (b : Nat) :
    PairwiseCoprimeABC 1 b (b + 1) := by
  simp [PairwiseCoprimeABC]

/-- The no-go gate *statement shape* is recorded as a predicate, not asserted: a positive
linear excess of repeated-prime mass along an unbounded adjacent family would disprove abc
(the source theorem `not_abcConjecture_of_adjacent_excessMass`; its proof was not fully
retrieved due to the fetch limit). -/
def AdjacentExcessMassGate (b : Nat → Nat) (δ K : ℝ) : Prop :=
  0 < δ ∧ δ < 1 ∧ (∀ n, 0 < b n) ∧
    (∀ B : ℝ, ∃ n : Nat, B < adjacentABCHeight (b n)) ∧
    (∀ n : Nat, (1 + δ) * adjacentABCHeight (b n) - K ≤ adjacentABCExcessMass (b n))

end

end IUTThreeClosures
