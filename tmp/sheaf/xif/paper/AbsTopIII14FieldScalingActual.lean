import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# STEP 0 prior-art: log_measure_prime_smul_finiteDimensional|measure_prime_smul_finiteDimensional -> hits LeanFormal/IUT/Foundations/LocalFields/FinitePadicHaarScaling.lean:25/:54 -> REUSE (field-scaling law, generic set S; no re-proof).

# [AbsTopIII] 14: field-scaling formula (generic region S, p-scaling) - PROVED

Corpus: papers/motizuki_corpus/text/Topics in Absolute Anabelian Geometry III.txt,
Prop 5.7 (i)(a) lines 7932-7935 (mu_k^log(m_k^n) = -f n log p) and (i)(b)
7938-7951 (scaling of the log-volume).
PROVED here, for an ARBITRARY region S with finite positive Haar mass:
  log mu(p * S) = -[K : Q_p] * log p + log mu(S),
and, if mu(S) = 1, log mu(p * S) = -[K : Q_p] * log p (residue form -f log p when
finrank = f).  This is the field-scaling content of Prop 5.7 at the concrete
p-adic local field, directly from the tree's FinitePadicHaarScaling API.
NAMED REMAINDER (not claimed): the normalization instance mu(O_K) = 1 is provided
separately by stage4 (AbsTopIII07NormalizedLocalVolumeActual.normalizedHaar_unitBall);
the n-fold iterate p^n * S and the unramified identification m_k^n = p^n * O_K
require positivity/finiteness of the scaled sets and the uniformizer API - records only.
-/

namespace LeanFormal.IUT.XiFPaper.AbsTopIII14FieldScalingActual

open MeasureTheory
open scoped Pointwise ENNReal
open LeanFormal.IUT.FinitePadicHaarScaling

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [ProperSpace K]
  [MeasurableSpace K] [CharZero K] [CompleteSpace K] [BorelSpace K]
  {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K]

/-- **Field-scaling law (generic region):** the log-volume of p * S shifts by
-[K : Q_p] * log p. -/
theorem fieldScaling_log_measure_prime_smul (μ : Measure K)
    [Measure.IsAddHaarMeasure μ] {S : Set K} (hpos : 0 < μ S) (hfin : μ S < ⊤) :
    Real.log (μ ((p : ℚ_[p]) • S)).toReal =
      (-(Module.finrank ℚ_[p] K : ℝ)) * Real.log (p : ℝ) +
        Real.log (μ S).toReal :=
  log_measure_prime_smul_finiteDimensional (p := p) μ hpos hfin

/-- **Normalized field-scaling law:** if mu(S) = 1 then log mu(p * S) = -[K:Q_p] log p. -/
theorem fieldScaling_log_measure_prime_smul_normalized (μ : Measure K)
    [Measure.IsAddHaarMeasure μ] {S : Set K} (hpos : 0 < μ S) (hfin : μ S < ⊤)
    (h1 : μ S = 1) :
    Real.log (μ ((p : ℚ_[p]) • S)).toReal =
      (-(Module.finrank ℚ_[p] K : ℝ)) * Real.log (p : ℝ) := by
  rw [fieldScaling_log_measure_prime_smul (p := p) μ hpos hfin, h1]
  simp

/-- **Residue form:** if the absolute degree equals f, the shift is -f log p. -/
theorem fieldScaling_log_measure_prime_smul_normalized_residue (μ : Measure K)
    [Measure.IsAddHaarMeasure μ] {S : Set K} (hpos : 0 < μ S) (hfin : μ S < ⊤)
    (h1 : μ S = 1) (f : ℕ) (hf : Module.finrank ℚ_[p] K = f) :
    Real.log (μ ((p : ℚ_[p]) • S)).toReal =
      (-(f : ℝ)) * Real.log (p : ℝ) := by
  rw [fieldScaling_log_measure_prime_smul_normalized (p := p) μ hpos hfin h1, hf]

/-- Named remainder rows (n-fold iterate; unramified identification; normalization). -/
def fieldScalingRemainderRows : List (String × String) :=
  [ ("n-fold p^n * S scaling",
      "NAMED REMAINDER: needs positivity/finiteness of scaled sets under p-steps")
  , ("m_k^n = p^n * O_K for unramified K/Q_p",
      "NAMED REMAINDER: needs uniformizer/maximal-ideal valuation API")
  , ("mu(O_K) = 1 normalization instance",
      "provided by stage4 AbsTopIII07NormalizedLocalVolumeActual.normalizedHaar_unitBall (PROVED)") ]

/-- The remainder record has three rows. -/
theorem fieldScalingRemainderRows_length : fieldScalingRemainderRows.length = 3 := rfl

#check fieldScaling_log_measure_prime_smul
#check fieldScaling_log_measure_prime_smul_normalized
#check fieldScaling_log_measure_prime_smul_normalized_residue
#check fieldScalingRemainderRows_length

end LeanFormal.IUT.XiFPaper.AbsTopIII14FieldScalingActual
end