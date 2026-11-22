/- Route 7.2: paperOrder to different bound conversion. -/
import tmp.sheaf.xif.paper.Mzk1G1PaperOrderBaseActual
import tmp.sheaf.xif.paper.Mzk1G1UniversalSeparationConstantActual
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentUpperBound
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PaperOrderBoundActual

open LeanFormal.IUT.XiFPaper.Mzk1G1PaperOrderBaseActual
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalSeparationConstantActual

variable {p : Nat} [Fact p.Prime]
variable {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L] [IsUltrametricDist L]
  [ProperSpace L] [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]

/-- The base log-shell ramification exponent at Q_p is one. -/
theorem logShellRamificationExponent_rat_eq_one :
    logShellRamificationExponent (K := ℚ_[p]) (p := p) = 1 := by
  unfold logShellRamificationExponent ramifiedPrimeAddVal
  haveI : IsDiscreteValuationRing (Integers ℚ_[p]) :=
    integersIsDiscreteValuationRing (p := p) (L := ℚ_[p])
  have hval : IsDiscreteValuationRing.addVal (Integers ℚ_[p]) (p : Integers ℚ_[p]) = 1 := by
    exact IsDiscreteValuationRing.addVal_uniformizer
      (show Irreducible (p : Integers ℚ_[p]) from by
        have h := PadicInt.irreducible_p (p := p)
        exact h)
  rw [hval]
  rfl

/-- Main conversion: the paper-normalized local different order of L/Q_p is at most
v_p([L:Q_p]) + 1. -/
theorem localDifferentPaperOrder_le_padicVal_finrank :
    localDifferentPaperOrder (p := p) (L := L) ≤
      (padicValNat p (Module.finrank ℚ_[p] L) : ℝ) + 1 := by
  have h := localDifferentPaperOrder_le_degree_padicVal (p := p) (K := ℚ_[p]) (L := L)
  rw [localDifferentPaperOrder_rat_eq_zero (p := p), logShellRamificationExponent_rat_eq_one (p := p)] at h
  simpa using h

#print axioms logShellRamificationExponent_rat_eq_one
#print axioms localDifferentPaperOrder_le_padicVal_finrank
end LeanFormal.IUT.XiFPaper.Mzk1G1PaperOrderBoundActual
