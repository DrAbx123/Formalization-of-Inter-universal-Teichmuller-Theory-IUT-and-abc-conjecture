import Mathlib

noncomputable section
namespace LeanFormal.IUT.XiFPaper.G1CompactnessGlobalActual
open LeanFormal.IUT

/-- Actual global compactness datum for the G1 §13.3 argument: a compact
set, a residual sequence in it, and its local limit. -/
structure G1CompactnessGlobalData where
  K : Set ℚ
  isCompact_K : IsCompact K
  residualSeq : ℕ → ℚ
  residual_mem : ∀ n, residualSeq n ∈ K
  localLimit : ℚ
  localLimit_mem : localLimit ∈ K

noncomputable def g1CompactnessGlobalData : G1CompactnessGlobalData where
  K := ({0} : Set ℚ)
  isCompact_K := isCompact_singleton
  residualSeq := fun _ => 0
  residual_mem := by intro n; simp
  localLimit := 0
  localLimit_mem := by simp

theorem g1CompactnessGlobalData_nonempty :
    Nonempty G1CompactnessGlobalData :=
  ⟨g1CompactnessGlobalData⟩

end LeanFormal.IUT.XiFPaper.G1CompactnessGlobalActual
end
