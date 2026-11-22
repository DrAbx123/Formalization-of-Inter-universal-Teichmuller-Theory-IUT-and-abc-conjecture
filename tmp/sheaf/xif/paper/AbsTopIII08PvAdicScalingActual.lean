import tmp.sheaf.xif.paper.S3137LogShellHaarLogVolumeScalingActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# STEP 0 prior-art: p_v-adic|logShellScale|localLogVolume|log_measure_prime_smul -> hits S3137LogShellHaarLogVolumeScalingActual (green): localLogVolume:46, log_measure_integralLogShell_eq:51, log_measure_prime_smul_integralLogShell:61, localLogVolume_prime_smul_integralLogShell:85, packetNormalization_log_measure_prime_smul_integralLogShell:96, finrank_one:109 -> REUSE (aliases only; no re-proof).

# [AbsTopIII] 08: Prop 5.7(i)(b) / Cor 5.10 p_v-adic log-volume scaling (PROVED in tree)

Corpus: papers/motizuki_corpus/text/Topics in Absolute Anabelian Geometry III.txt.
Prop 5.7 (i)(a) 7932-7935: residue cardinality p^f gives mu_k^log(m_k^n) = -f n log p;
(i)(b) 7938-7951 scaling mu_k^log(x*A) = mu_k^log(A) + muDot_k^log(x).
Concrete tree realization: the actual p-scaling law for the integral log-shell
over a finite-dimensional p-adic local field K is PROVED in
S3137LogShellHaarLogVolumeScalingActual (IUT III Prop 3.9(i) normalization):
log mu(p * integralLogShell) = -(finrank)*log p + log mu(integralLogShell).
Re-exported here (no re-proof) as the [AbsTopIII] p_v-adic row.
-/

namespace LeanFormal.IUT.XiFPaper.AbsTopIII08PvAdicScalingActual

open LeanFormal.IUT.XiFPaper.S3137LogShellHaarLogVolumeScalingActual
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.FinitePadicHaarScaling
open MeasureTheory
open scoped Pointwise ENNReal
open scoped Pointwise
open MeasureTheory

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [ProperSpace K]
  [MeasurableSpace K] [CharZero K] [CompleteSpace K] [BorelSpace K]
  {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K]

/-- Prop 5.7(i)(b)/Cor 5.10 p_v-adic scaling of the actual integral log-shell
(reused from S3137LogShellHaarLogVolumeScalingActual:61). -/
theorem absTopIII_log_measure_prime_smul_integralLogShell (μ : Measure K)
    [Measure.IsAddHaarMeasure μ] :
    Real.log (μ ((p : ℚ_[p]) •
      (integralLogShell (K := K) (p := p) : Set K))).toReal =
    -((Module.finrank ℚ_[p] K : ℝ) * Real.log (p : ℝ)) +
    Real.log (μ (integralLogShell (K := K) (p := p) : Set K)).toReal :=
  log_measure_prime_smul_integralLogShell (K := K) (p := p) μ

/-- The local log-volume form of the same scaling law (reused from :85). -/
theorem absTopIII_localLogVolume_prime_smul_integralLogShell (μ : Measure K)
    [Measure.IsAddHaarMeasure μ] :
    localLogVolume μ ((p : ℚ_[p]) •
      (integralLogShell (K := K) (p := p) : Set K)) =
    -((Module.finrank ℚ_[p] K : ℝ) * Real.log (p : ℝ)) +
    localLogVolume μ (integralLogShell (K := K) (p := p) : Set K) :=
  localLogVolume_prime_smul_integralLogShell (K := K) (p := p) μ

/-- In the normalized-weight (finrank one) case the p-scaling shift is exactly
-log p, i.e. the packet normalization of IUT III, Proposition 3.9, (i). -/
theorem absTopIII_localLogVolume_prime_smul_finrank_one
    (h1 : Module.finrank ℚ_[p] K = 1) (μ : Measure K)
    [Measure.IsAddHaarMeasure μ] :
    localLogVolume μ ((p : ℚ_[p]) •
      (integralLogShell (K := K) (p := p) : Set K)) =
    -Real.log (p : ℝ) +
    localLogVolume μ (integralLogShell (K := K) (p := p) : Set K) :=
  localLogVolume_prime_smul_integralLogShell_finrank_one (K := K) (p := p) h1 μ

#check absTopIII_log_measure_prime_smul_integralLogShell
#check absTopIII_localLogVolume_prime_smul_integralLogShell
#check absTopIII_localLogVolume_prime_smul_finrank_one

end LeanFormal.IUT.XiFPaper.AbsTopIII08PvAdicScalingActual