import LeanFormal.IUT.ABCBridge.Arithmetic.LogarithmicBoundEquivalence
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1ABCLogRpowActual — ABC log bound <-> multiplicative rpow bound

DAG node: iutiv-abc:G0.log.  The additive log bound log c <= (1+eps) log rad + A
is equivalent to the multiplicative bound c <= K * rad^(1+eps) with K = exp A
(and K > 0).  This is the exponential form used by the ABC literature; it is an
elementary equivalence, no new arithmetic input.

No closure claim; GATE NOT PASSED; registry 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCLogRpowActual

open LeanFormal.IUT

/-- Multiplicative rpow form of the fixed-constant ABC bound. -/
def ABCRpowBound (epsilon K : Real) : Prop :=
  ∀ a b c : Nat, IsABCTriple a b c →
    (c : Real) ≤ K * (radical (a * b * c) : Real) ^ (1 + epsilon)

/-- Additive log bound implies the rpow bound with K = exp A. -/
theorem rpowBound_of_abcLogBound {epsilon A : Real} (h : ABCLogBound epsilon A) :
    ABCRpowBound epsilon (Real.exp A) := by
  intro a b c habc
  have h1 := h a b c habc
  have hcpos : (0 : Real) < (c : Real) := abcTriple_c_pos habc
  have hrpos : (0 : Real) < (radical (a * b * c) : Real) := radical_cast_pos a b c
  have hle : (c : Real) ≤ Real.exp ((1 + epsilon) * Real.log (radical (a * b * c) : Real) + A) :=
    (Real.log_le_iff_le_exp hcpos).mp h1
  have hrpow : Real.exp ((1 + epsilon) * Real.log (radical (a * b * c) : Real)) =
      (radical (a * b * c) : Real) ^ (1 + epsilon) := by
    rw [Real.rpow_def_of_pos hrpos]
    congr 1
    ring
  calc (c : Real) ≤ Real.exp ((1 + epsilon) * Real.log (radical (a * b * c) : Real) + A) := hle
    _ = Real.exp A * (radical (a * b * c) : Real) ^ (1 + epsilon) := by
        rw [Real.exp_add, hrpow, mul_comm]

/-- The rpow bound with positive K implies the log bound with A = log K. -/
theorem abcLogBound_of_rpowBound {epsilon K : Real} (hK : 0 < K)
    (h : ABCRpowBound epsilon K) : ABCLogBound epsilon (Real.log K) := by
  intro a b c habc
  have h1 := h a b c habc
  have hcpos : (0 : Real) < (c : Real) := abcTriple_c_pos habc
  have hrpos : (0 : Real) < (radical (a * b * c) : Real) := radical_cast_pos a b c
  have hrpow : Real.exp ((1 + epsilon) * Real.log (radical (a * b * c) : Real)) =
      (radical (a * b * c) : Real) ^ (1 + epsilon) := by
    rw [Real.rpow_def_of_pos hrpos]
    congr 1
    ring
  have hle : (c : Real) ≤ Real.exp ((1 + epsilon) * Real.log (radical (a * b * c) : Real) +
      Real.log K) := by
    calc (c : Real) ≤ K * (radical (a * b * c) : Real) ^ (1 + epsilon) := h1
      _ = Real.exp (Real.log K) * (radical (a * b * c) : Real) ^ (1 + epsilon) := by
          rw [Real.exp_log hK]
      _ = Real.exp ((1 + epsilon) * Real.log (radical (a * b * c) : Real) + Real.log K) := by
          rw [Real.exp_add, hrpow, mul_comm]
  exact (Real.log_le_iff_le_exp hcpos).mpr hle

/-- Conjecture-level equivalence with positive multiplicative constants. -/
theorem abcLogConjecture_iff_rpowConjecture :
    ABCLogConjecture ↔
      (∀ epsilon : Real, 0 < epsilon → ∃ K : Real, 0 < K ∧ ABCRpowBound epsilon K) := by
  constructor
  · intro h epsilon hepsilon
    obtain ⟨A, hA⟩ := h epsilon hepsilon
    exact ⟨Real.exp A, Real.exp_pos A, rpowBound_of_abcLogBound hA⟩
  · intro h epsilon hepsilon
    obtain ⟨K, hK, hKb⟩ := h epsilon hepsilon
    exact ⟨Real.log K, abcLogBound_of_rpowBound hK hKb⟩

/-- Rows: log/rpow status. -/
def abcLogRpowRows : List (String × String × String) :=
  [ ("log -> rpow", "rpowBound_of_abcLogBound", "PROVED (K = exp A)"),
    ("rpow -> log", "abcLogBound_of_rpowBound", "PROVED (A = log K, K > 0)"),
    ("conjecture equivalence", "abcLogConjecture_iff_rpowConjecture", "PROVED"),
    ("scope", "elementary equivalence; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem abcLogRpowRows_length : abcLogRpowRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ABCLogRpowActual

end
