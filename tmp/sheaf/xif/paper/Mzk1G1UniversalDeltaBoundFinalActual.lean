/- Route 7.2: final explicit bound delta <= d*(v_p(d)+1). -/
import tmp.sheaf.xif.paper.Mzk1G1UniversalLogShellBoundActual
import tmp.sheaf.xif.paper.Mzk1G1UniversalSeparationConstantActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1UniversalDeltaBoundFinalActual

open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalDeltaBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalLogShellBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalSeparationConstantActual

variable {p : Nat} [Fact p.Prime]
variable {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L] [IsUltrametricDist L]
  [ProperSpace L] [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]

/-- The local different order is bounded by the explicit constant B. -/
theorem localDifferentOrder_le_differentBound :
    (localDifferentOrder (p := p) (L := L) : ℝ) ≤
      (differentBound p (Module.finrank ℚ_[p] L) : ℝ) := by
  have h1 := localDifferentOrder_le_padicVal_mul_logShell (p := p) (L := L)
  have h2 : (logShellRamificationExponent (K := L) (p := p) : ℝ) ≤
      (Module.finrank ℚ_[p] L : ℝ) := by
    exact_mod_cast logShellRamificationExponent_le_finrank (p := p) (L := L)
  have h3 : (0 : ℝ) ≤ (padicValNat p (Module.finrank ℚ_[p] L) : ℝ) + 1 := by positivity
  have h4 : (localDifferentOrder (p := p) (L := L) : ℝ) ≤
      ((padicValNat p (Module.finrank ℚ_[p] L) : ℝ) + 1) *
        (Module.finrank ℚ_[p] L : ℝ) := by
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_left h2 h3
  unfold differentBound
  push_cast
  exact h4

#print axioms localDifferentOrder_le_differentBound
end LeanFormal.IUT.XiFPaper.Mzk1G1UniversalDeltaBoundFinalActual
