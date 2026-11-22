/- Route 7.2: from the paperOrder bound to the actual local different order bound. -/
import tmp.sheaf.xif.paper.Mzk1G1PaperOrderBoundActual
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentUpperBound
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1UniversalDeltaBoundActual

open LeanFormal.IUT.XiFPaper.Mzk1G1PaperOrderBoundActual
open LeanFormal.IUT.IntegralTraceDualTensorInclusion

variable {p : Nat} [Fact p.Prime]
variable {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L] [IsUltrametricDist L]
  [ProperSpace L] [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]

/-- The actual local different order is bounded by (v_p(d)+1) times the ramification exponent. -/
theorem localDifferentOrder_le_padicVal_mul_logShell :
    (localDifferentOrder (p := p) (L := L) : ℝ) ≤
      ((padicValNat p (Module.finrank ℚ_[p] L) : ℝ) + 1) *
        (logShellRamificationExponent (K := L) (p := p) : ℝ) := by
  have hp := localDifferentPaperOrder_le_padicVal_finrank (p := p) (L := L)
  have he : (0 : ℝ) < (logShellRamificationExponent (K := L) (p := p) : ℝ) := by
    haveI : IsDiscreteValuationRing (Integers L) :=
      integersIsDiscreteValuationRing (p := p) (L := L)
    exact_mod_cast logShellRamificationExponent_pos (K := L) (p := p)
  have hdef : localDifferentPaperOrder (p := p) (L := L) =
      (localDifferentOrder (p := p) (L := L) : ℝ) /
        (logShellRamificationExponent (K := L) (p := p) : ℝ) := rfl
  rw [hdef, div_le_iff₀ he] at hp
  exact hp

#print axioms localDifferentOrder_le_padicVal_mul_logShell
end LeanFormal.IUT.XiFPaper.Mzk1G1UniversalDeltaBoundActual
