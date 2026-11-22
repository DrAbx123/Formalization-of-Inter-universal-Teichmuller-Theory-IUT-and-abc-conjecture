/- Route 7.2: direct different bound without the base paperOrder computation (retry).

Reuse / 查重:
* LeanFormal.IUT.LocalDifferentUpperBound.localDifferentPaperOrder_le_degree_padicVal
  (DONE) gives paperOrder_L <= paperOrder_Qp + v_p(d) + 1/e.
* The base term is only used with its NONNEGATIVITY (paperOrder = order/e >= 0),
  so no exact base different computation is needed.
* LeanFormal.IUT.LocalDifferentUpperBound.logShellRamificationExponent_eq_ramificationIdx
  (DONE) + Mathlib ramificationIdx_le_finrank give e <= [L:Q_p].
-/
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentUpperBound
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellRamificationInertia
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1UniversalDifferentBoundDirectActual

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open LeanFormal.IUT.LocalDifferentUpperBound
open LeanFormal.IUT.LocalFieldLogarithm

variable {p : Nat} [Fact p.Prime]
variable {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L] [IsUltrametricDist L]
  [ProperSpace L] [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]

/-- The base paper-normalized different order is nonnegative (it is order / e). -/
theorem localDifferentPaperOrder_rat_nonneg :
    0 ≤ localDifferentPaperOrder (p := p) (L := ℚ_[p]) := by
  unfold localDifferentPaperOrder
  positivity

/-- e <= [L:Q_p]. -/
theorem logShellRamificationExponent_le_finrank' :
    logShellRamificationExponent (K := L) (p := p) ≤ Module.finrank ℚ_[p] L := by
  letI : IsIntegralClosure (Integers L) ℤ_[p] L := IsIntegralClosure.of_isIntegrallyClosed _ _ _
  letI : IsDiscreteValuationRing (Integers L) := integersIsDiscreteValuationRing (p := p) (L := L)
  letI : IsDedekindDomain (Integers L) := integersIsDedekindDomain (p := p) (L := L)
  letI : Module.Finite ℤ_[p] (Integers L) := integersModuleFinite (p := p) (L := L)
  letI : Module.IsTorsionFree ℤ_[p] (Integers L) := integersIsTorsionFree (p := p) (L := L)
  letI : (IsLocalRing.maximalIdeal (Integers L)).LiesOver (IsLocalRing.maximalIdeal ℤ_[p]) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap ℤ_[p] (Integers L))).symm⟩
  rw [logShellRamificationExponent_eq_ramificationIdx (K := L) (p := p)]
  have h := Ideal.ramificationIdx_le_finrank
    (R := ℤ_[p]) (S := Integers L) (K := ℚ_[p]) (L := FractionRing (Integers L))
    (p := IsLocalRing.maximalIdeal ℤ_[p]) (P := IsLocalRing.maximalIdeal (Integers L))
  rw [fractionRing_integer_degree_eq (K := ℚ_[p]) (L := L)] at h
  exact h

/-- Main: paper order differs from v_p(d)+1 only by a nonnegative base term and 1/e <= 1. -/
theorem localDifferentPaperOrder_le_padicVal_succ
    (hbase0 : localDifferentPaperOrder (p := p) (L := ℚ_[p]) = 0) :
    localDifferentPaperOrder (p := p) (L := L) ≤
      (padicValNat p (Module.finrank ℚ_[p] L) : ℝ) + 1 := by
  have h := localDifferentPaperOrder_le_degree_padicVal (p := p) (K := ℚ_[p]) (L := L)
  have hbase : localDifferentPaperOrder (p := p) (L := ℚ_[p]) = 0 := hbase0
  have hepos : 0 < logShellRamificationExponent (K := ℚ_[p]) (p := p) :=
    logShellRamificationExponent_pos (K := ℚ_[p]) (p := p)
  have he1 : (1 : ℝ) ≤ (logShellRamificationExponent (K := ℚ_[p]) (p := p) : ℝ) := by
    exact_mod_cast hepos
  have hrec : (1 : ℝ) / (logShellRamificationExponent (K := ℚ_[p]) (p := p) : ℝ) ≤ 1 := by
    rw [div_le_iff₀ (by exact_mod_cast hepos)]
    simpa using he1
  linarith [h, hbase, hrec]

/-- localDifferentOrder = paperOrder * e (definition of the paper normalization). -/
theorem localDifferentOrder_cast_eq_paperOrder_mul :
    (localDifferentOrder (p := p) (L := L) : ℝ) =
      localDifferentPaperOrder (p := p) (L := L) *
        (logShellRamificationExponent (K := L) (p := p) : ℝ) := by
  have he : (logShellRamificationExponent (K := L) (p := p) : ℝ) ≠ 0 := by
    exact_mod_cast (logShellRamificationExponent_pos (K := L) (p := p)).ne'
  unfold localDifferentPaperOrder
  field_simp

/-- Direct bound: localDifferentOrder <= d * (v_p(d) + 2) with d = [L:Q_p]. -/
theorem localDifferentOrder_le_differentBound
    (hbase0 : localDifferentPaperOrder (p := p) (L := ℚ_[p]) = 0) :
    localDifferentOrder (p := p) (L := L) ≤
      Module.finrank ℚ_[p] L * (padicValNat p (Module.finrank ℚ_[p] L) + 2) := by
  let d := Module.finrank ℚ_[p] L
  have he : logShellRamificationExponent (K := L) (p := p) ≤ d :=
    logShellRamificationExponent_le_finrank'
  have hpaper := localDifferentPaperOrder_le_padicVal_succ (p := p) (L := L) hbase0
  have hcast := localDifferentOrder_cast_eq_paperOrder_mul (p := p) (L := L)
  have heR : (0 : ℝ) ≤ (logShellRamificationExponent (K := L) (p := p) : ℝ) := by positivity
  have hboundR : (localDifferentOrder (p := p) (L := L) : ℝ) ≤
      (d : ℝ) * (((padicValNat p d : ℕ) : ℝ) + 2) := by
    have h1 : localDifferentPaperOrder (p := p) (L := L) *
        (logShellRamificationExponent (K := L) (p := p) : ℝ) ≤
        (((padicValNat p d : ℕ) : ℝ) + 1) * (d : ℝ) := by
      apply mul_le_mul hpaper (by exact_mod_cast he) heR
      positivity
    rw [hcast]
    calc localDifferentPaperOrder (p := p) (L := L) *
        (logShellRamificationExponent (K := L) (p := p) : ℝ)
        ≤ (((padicValNat p d : ℕ) : ℝ) + 1) * (d : ℝ) := h1
      _ ≤ (d : ℝ) * (((padicValNat p d : ℕ) : ℝ) + 2) := by
          nlinarith [show (0:ℝ) ≤ (d:ℝ) by positivity]
  exact_mod_cast hboundR

#print axioms localDifferentOrder_le_differentBound
end LeanFormal.IUT.XiFPaper.Mzk1G1UniversalDifferentBoundDirectActual
