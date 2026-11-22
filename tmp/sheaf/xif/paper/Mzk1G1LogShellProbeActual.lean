import tmp.sheaf.xif.paper.Mzk1G1LocalFieldInstancesActual -- requires olean (retry 3)
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellRamificationInertia
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentUpperBound
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Instances
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1LogShellProbeActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open LeanFormal.IUT.LocalDifferentUpperBound
open LeanFormal.IUT.LocalFieldLogarithm
variable {p : Nat} [Fact p.Prime]
variable {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L] [IsUltrametricDist L]
  [ProperSpace L] [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
local instance : Algebra (FractionRing ℤ_[p]) (FractionRing (Integers L)) :=
  FractionRing.liftAlgebra ℤ_[p] (FractionRing (Integers L))
example : logShellRamificationExponent (K := L) (p := p) ≤ Module.finrank ℚ_[p] L := by
  letI : IsIntegrallyClosed ℤ_[p] := padicInt_isIntegrallyClosed (p := p)
  letI : IsDedekindDomain ℤ_[p] := by infer_instance
  letI : IsDedekindDomain (Integers L) := integersIsDedekindDomain (p := p) (L := L)
  letI : Module.IsTorsionFree ℤ_[p] (Integers L) := integersIsTorsionFree (p := p) (L := L)

  letI : (IsLocalRing.maximalIdeal (Integers L)).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal (Integers L)).isPrime
  letI : (IsLocalRing.maximalIdeal (Integers L)).LiesOver (IsLocalRing.maximalIdeal ℤ_[p]) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap ℤ_[p] (Integers L))).symm⟩
  rw [logShellRamificationExponent_eq_ramificationIdx (K := L) (p := p)]
  have h := Ideal.ramificationIdx_le_finrank (R := ℤ_[p]) (S := Integers L)
    (K := FractionRing ℤ_[p]) (L := FractionRing (Integers L))
    (p := IsLocalRing.maximalIdeal ℤ_[p]) (P := IsLocalRing.maximalIdeal (Integers L))
  rw [fractionRing_integer_degree_eq (K := ℚ_[p]) (L := L)] at h
  exact h
end LeanFormal.IUT.XiFPaper.Mzk1G1LogShellProbeActual
