/- R5 K=Q_p ramification bound interface (OPEN item, no sorry).

The actual proof e <= [L:Q_p] needs the K=Q_p local Algebra instance and the
fraction-ring finrank bridge.  Until that is completed, the bound is recorded as an
explicit input structure (route 7.1(3) style), NOT as a bare sorry; consumers pass it.
-/
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentUpperBound
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellRamificationInertia
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1ProbeKQpActual

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open LeanFormal.IUT.LocalFieldLogarithm

variable {p : Nat} [Fact p.Prime]
variable {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L] [IsUltrametricDist L]
  [ProperSpace L] [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]

/-- Explicit input: the K = Q_p ramification bound e <= [L:Q_p].
(OPEN: the actual proof needs the K=Q_p local Algebra/fraction-ring bridge.) -/
structure KQpRamificationBound : Prop where
  bound : logShellRamificationExponent (K := L) (p := p) ≤ Module.finrank ℚ_[p] L

/-- The K=Q_p ramification bound, from the explicit input structure. -/
theorem logShellRamificationExponent_le_finrank_KQp
    (H : KQpRamificationBound (p := p) (L := L)) :
    logShellRamificationExponent (K := L) (p := p) ≤ Module.finrank ℚ_[p] L :=
  H.bound

#print axioms logShellRamificationExponent_le_finrank_KQp
end LeanFormal.IUT.XiFPaper.Mzk1G1ProbeKQpActual
