/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentNormOrder
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds
import Mathlib.Tactic

/-! # A798 hull: dictionary of the different/unit term `diff = log N(d)`

Green `LocalDifferentNormOrder` gives

  `||localDifferentGenerator|| = p ^ (-localDifferentPaperOrder)`,
  `localNormOrder localDifferentGenerator = localDifferentPaperOrder`,

so `log N(d) = -d_v · log p` with `d_v = localDifferentPaperOrder`.
`LocalDifferentUpperBound` gives `localDifferentPaperOrder_le_degree_padicVal`.
`DifferentTraceProduct.traceMultiplierIdeal_eq_differentIdeal` identifies the
trace-dual lattice with the different ideal.  Torsion is `r/n`, arch is
`log(sqrt 2 * pi)`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1DifferentDictionaryActual

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open LeanFormal.IUT.LocalDifferentUpperBound
open LeanFormal.IUT.LocalDifferentNormOrder

universe u

/-- `log N(d)` in locally compact `Q_p`-spaces is `-paperOrder · log p`. -/
theorem log_norm_differentGenerator_eq_neg_paperOrder_mul_log
    {p : ℕ} [Fact p.Prime]
    {K : Type u} [NormedField K] [CharZero K] [CompleteSpace K]
    [IsUltrametricDist K] [ProperSpace K] [NormedAlgebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] :
    Real.log ‖(localDifferentGenerator (p := p) (L := K) : K)‖ =
      -localDifferentPaperOrder (p := p) (L := K) * Real.log (p : ℝ) := by
  rw [norm_differentGenerator_eq_prime_rpow_neg_paperOrder (p := p) (K := K)]
  rw [Real.log_rpow (by exact_mod_cast (Fact.out : p.Prime).pos)]

/-- The paper `diff = log N(d)` term. -/
def diffPaperLog (order logp : ℝ) : ℝ := -order * logp

theorem diffPaperLog_eq (order logp : ℝ) :
    diffPaperLog order logp = -order * logp := rfl

/-- Paper per-place different term (finite place). -/
def diffPaperPerPlace (order logp torsion arch : ℝ) : ℝ :=
  -order * logp - torsion + arch

/-- Torsion constant `r/n`. -/
def torsionConstant (r n : ℝ) : ℝ := r / n

/-- Archimedean constant `log(sqrt 2 * pi)`. -/
def archConstant : ℝ := Real.log (Real.sqrt 2 * Real.pi)

theorem archConstant_eq : archConstant = Real.log (Real.sqrt 2 * Real.pi) := rfl

theorem archConstant_eq_log : archConstant = Real.log 2 / 2 + Real.log Real.pi := by
  unfold archConstant
  rw [Real.log_mul (by positivity) Real.pi_ne_zero,
    Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The paper per-place dictionary `diff_v = log N(d_v) - r_v/n_v + log(sqrt 2 pi)`. -/
theorem diffPaperPerPlace_eq (order logp r n : ℝ) :
    diffPaperPerPlace order logp (torsionConstant r n) archConstant =
      -order * logp - r / n + Real.log (Real.sqrt 2 * Real.pi) := by
  unfold diffPaperPerPlace torsionConstant archConstant
  ring

/-- The different term is the negative of the paper order times `log p`. -/
theorem diffPaperPerPlace_different_eq (order logp r n : ℝ) :
    diffPaperPerPlace order logp (torsionConstant r n) archConstant - archConstant +
      torsionConstant r n = -order * logp := by
  unfold diffPaperPerPlace torsionConstant archConstant
  ring

def differentRows : List (String × String × String) :=
  [ ("log N(d)", "log||localDifferentGenerator|| = -localDifferentPaperOrder*log p", "PROVED (log_norm_differentGenerator_eq_neg_paperOrder_mul_log)"),
    ("norm order", "||localDifferentGenerator|| = p^(-localDifferentPaperOrder)", "GREEN (norm_differentGenerator_eq_prime_rpow_neg_paperOrder)"),
    ("localNormOrder", "localNormOrder localDifferentGenerator = localDifferentPaperOrder", "GREEN (localNormOrder_differentGenerator_eq_paperOrder)"),
    ("different upper bound", "localDifferentPaperOrder <= degree + padicVal + 1/e", "GREEN (localDifferentPaperOrder_le_degree_padicVal)"),
    ("trace-dual lattice", "traceMultiplierIdeal = differentIdeal", "GREEN (DifferentTraceProduct.traceMultiplierIdeal_eq_differentIdeal)"),
    ("torsion constant", "torsion = r/n", "DEF (torsionConstant)"),
    ("arch constant", "arch = log(sqrt 2*pi) = log2/2 + log pi", "PROVED (archConstant_eq_log)"),
    ("per-place dictionary", "diff_v = -order*logp - r/n + log(sqrt2*pi)", "PROVED (diffPaperPerPlace_eq)"),
    ("needed facts", "paper order d_v from LocalDifferentNormOrder; upper bound from IntegralLogShellSharpBounds A/B; r,n actual torsion invariants", "GREEN/INPUT") ]

theorem differentRows_length : differentRows.length = 9 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1DifferentDictionaryActual.log_norm_differentGenerator_eq_neg_paperOrder_mul_log
#print axioms LeanFormal.IUT.XiFPaper.Mzk1DifferentDictionaryActual.archConstant_eq_log
#print axioms LeanFormal.IUT.XiFPaper.Mzk1DifferentDictionaryActual.diffPaperPerPlace_eq

end LeanFormal.IUT.XiFPaper.Mzk1DifferentDictionaryActual

end