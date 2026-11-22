import Mathlib

/-!
# Mzk1P1CardinalityActual — specialSet {∞,0,1} distinctness/finiteness (genuine)

Status: PENDING-VERIFY (watchdog compile). No sorry, no axiom, no fake closure.
Corrected target vocabulary: P1Point K := Option K; specialSet = {none, some 0, some 1}.
Proves distinctness and finiteness of the special set (genuine finite set facts). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1P1CardinalityActual

/-- The three special points as a Set in P1(ℂ). -/
def specialSet : Set (Option ℂ) := {none, some (0 : ℂ), some (1 : ℂ)}

/-- Infinity is not 0 (genuine). -/
theorem infty_ne_finite_zero : (none : Option ℂ) ≠ some (0 : ℂ) := by
  simp

/-- 0 and 1 are distinct finite points (genuine). -/
theorem finite_zero_ne_finite_one : (some (0 : ℂ) : Option ℂ) ≠ some (1 : ℂ) := by
  simp

/-- The special set is finite (genuine). -/
theorem specialSet_finite : specialSet.Finite := by
  simp [specialSet]

/-- Infinity belongs to the special set (genuine). -/
theorem infty_mem_specialSet : (none : Option ℂ) ∈ specialSet := by
  simp [specialSet]

/-- 0 belongs to the special set (genuine). -/
theorem zero_mem_specialSet : (some (0 : ℂ) : Option ℂ) ∈ specialSet := by
  simp [specialSet]

/-- 1 belongs to the special set (genuine). -/
theorem one_mem_specialSet : (some (1 : ℂ) : Option ℂ) ∈ specialSet := by
  simp [specialSet]

end LeanFormal.IUT.XiFPaper.Mzk1P1CardinalityActual
