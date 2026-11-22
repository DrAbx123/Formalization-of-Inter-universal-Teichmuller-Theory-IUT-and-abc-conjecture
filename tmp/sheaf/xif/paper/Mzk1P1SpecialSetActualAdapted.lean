import Mathlib

/-!
# Mzk1P1SpecialSetActualAdapted (adapted copy, A475 reuse) — P1 points (Option ℂ) and specialSet {∞,0,1} (definitions + genuine membership lemmas)

Status: PENDING-VERIFY (watchdog compile). No sorry, no axiom, no fake closure.
Corrected target vocabulary: P1Point K := Option K; infty := none; ofFinite := some;
specialSet = {∞, 0, 1} as a Set (Option ℂ). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1P1SpecialSetActualAdapted

/-- P1 points over a field K, represented as Option K (none = infinity). -/
abbrev P1Point (K : Type*) := Option K

/-- Infinity point. -/
def P1Point.infty {K : Type*} : P1Point K := none

/-- Finite point from K. -/
def P1Point.ofFinite {K : Type*} (x : K) : P1Point K := some x

/-- The special set {∞, 0, 1} in P1(ℂ). -/
def specialSet : Set (P1Point ℂ) := {P1Point.infty, P1Point.ofFinite 0, P1Point.ofFinite 1}

/-- Infinity is in the special set (genuine). -/
theorem infty_mem_specialSet : P1Point.infty ∈ specialSet := by
  simp [specialSet]

/-- 0 is in the special set (genuine). -/
theorem zero_mem_specialSet : P1Point.ofFinite (0 : ℂ) ∈ specialSet := by
  simp [specialSet]

/-- 1 is in the special set (genuine). -/
theorem one_mem_specialSet : P1Point.ofFinite (1 : ℂ) ∈ specialSet := by
  simp [specialSet]

/-- The special set is finite (genuine). -/
theorem specialSet_finite : specialSet.Finite := by
  simp [specialSet]

end LeanFormal.IUT.XiFPaper.Mzk1P1SpecialSetActualAdapted
