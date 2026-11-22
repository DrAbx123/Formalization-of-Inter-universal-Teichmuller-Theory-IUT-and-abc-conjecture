/- Route 7.2: the ramification exponent of L/Q_p is at most the field degree. -/
import tmp.sheaf.xif.paper.Mzk1G1UniversalDeltaBoundActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellRamificationInertia
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1UniversalLogShellBoundActual

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open LeanFormal.IUT.LocalDifferentUpperBound
open LeanFormal.IUT.XiFPaper.Mzk1G1PaperOrderBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalDeltaBoundActual

variable {p : Nat} [Fact p.Prime]
variable {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L] [IsUltrametricDist L]
  [ProperSpace L] [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]

/-- The ramification exponent of L/Q_p is at most the field degree. -/
theorem logShellRamificationExponent_le_finrank :
    logShellRamificationExponent (K := L) (p := p) ≤ Module.finrank ℚ_[p] L := by
  letI : IsIntegrallyClosed ℤ_[p] := padicInt_isIntegrallyClosed (p := p)
  letI : IsDedekindDomain ℤ_[p] := by infer_instance
  letI : IsDedekindDomain (Integers L) := integersIsDedekindDomain (p := p) (L := L)
  letI : Module.IsTorsionFree ℤ_[p] (Integers L) := integersIsTorsionFree (p := p) (L := L)
  letI : NoZeroSMulDivisors ℤ_[p] (Integers L) := by infer_instance
  letI : (IsLocalRing.maximalIdeal (Integers L)).IsPrime := inferInstance
  letI : (IsLocalRing.maximalIdeal (Integers L)).LiesOver (IsLocalRing.maximalIdeal ℤ_[p]) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap ℤ_[p] (Integers L))).symm⟩
  rw [LeanFormal.IUT.LocalDifferentUpperBound.logShellRamificationExponent_eq_ramificationIdx (K := L) (p := p)]
  exact IsDedekindDomain.ramificationIdx_le_finrank (K := FractionRing ℤ_[p])
    (L := FractionRing (Integers L)) (IsLocalRing.maximalIdeal (Integers L))

#print axioms logShellRamificationExponent_le_finrank
end LeanFormal.IUT.XiFPaper.Mzk1G1UniversalLogShellBoundActual
