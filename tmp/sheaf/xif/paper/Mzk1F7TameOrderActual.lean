import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentNormOrder
import Mathlib.Tactic
/-!
# F7 tame local bridge (route §8.5): normalized different order ≤ 1 in the tame case

The Dedekind-level tame equality (repo donor
`LeanFormal.IUT.IUTIV.Estimates.count_differentIdeal_eq_of_tame`) gives, for a
tamely ramified local extension, different order `d = e - 1`
(`e = logShellRamificationExponent`). This file records the arithmetic end:
the paper-normalized order `d/e` is at most `1`, hence the per-prime
contribution `(d/e) * log p` is at most `log p` (route §8.5 tame case).

Lead lane: H-T / P8-P.
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1F7TameOrderActual

open LeanFormal.IUT.LocalFieldIntegralUnits LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open LeanFormal.IUT.LocalDifferentUpperBound LeanFormal.IUT.LocalDifferentNormOrder
open UniqueFactorizationMonoid IsLocalRing

variable {p : ℕ} [Fact p.Prime]
variable {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L]
  [IsUltrametricDist L] [ProperSpace L] [NormedAlgebra ℚ_[p] L]
  [FiniteDimensional ℚ_[p] L]

/-- Arithmetic end of the tame local bridge. -/
theorem localDifferentPaperOrder_le_one_of_differentOrder_eq
    (h : localDifferentOrder (p := p) (L := L) =
      logShellRamificationExponent (K := L) (p := p) - 1) :
    localDifferentPaperOrder (p := p) (L := L) ≤ 1 := by
  have he : 0 < logShellRamificationExponent (K := L) (p := p) :=
    logShellRamificationExponent_pos (K := L) (p := p)
  have heR : (0 : ℝ) < (logShellRamificationExponent (K := L) (p := p) : ℝ) := by
    exact_mod_cast he
  unfold localDifferentPaperOrder
  rw [h, div_le_iff₀ heR]
  have hle : ((logShellRamificationExponent (K := L) (p := p) - 1 : ℕ) : ℝ) ≤
      (logShellRamificationExponent (K := L) (p := p) : ℝ) := by
    exact_mod_cast Nat.sub_le _ _
  nlinarith

section FactorCount

variable [IsDiscreteValuationRing (Integers L)]

/-- Tame input in the form produced by `count_differentIdeal_eq_of_tame`: the
multiplicity of the maximal ideal in the local different ideal is `e - 1`. -/
theorem localDifferentPaperOrder_le_one_of_factorCount_eq
    (h : (normalizedFactors (differentIdeal ℤ_[p] (Integers L))).count
        (maximalIdeal (Integers L)) =
      logShellRamificationExponent (K := L) (p := p) - 1) :
    localDifferentPaperOrder (p := p) (L := L) ≤ 1 := by
  have horder : localDifferentOrder (p := p) (L := L) =
      (normalizedFactors (differentIdeal ℤ_[p] (Integers L))).count
        (maximalIdeal (Integers L)) :=
    localDifferentOrder_eq_factorCount (p := p) (K := L)
  exact localDifferentPaperOrder_le_one_of_differentOrder_eq (horder.trans h)

/-- Route §8.5 tame per-prime bound: the normalized tame different contribution
is at most `log p`. -/
theorem tame_localDifferent_contribution_le_log
    (h : localDifferentOrder (p := p) (L := L) =
      logShellRamificationExponent (K := L) (p := p) - 1) :
    localDifferentPaperOrder (p := p) (L := L) * Real.log (p : ℝ) ≤ Real.log (p : ℝ) := by
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hle := localDifferentPaperOrder_le_one_of_differentOrder_eq (L := L) h
  simpa [mul_comm] using mul_le_of_le_one_right hlog.le hle

end FactorCount

end LeanFormal.IUT.XiFPaper.Mzk1F7TameOrderActual
