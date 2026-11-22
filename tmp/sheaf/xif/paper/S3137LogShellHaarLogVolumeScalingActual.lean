import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellHaarIndex

/-!
# S3137: log-volume normalization for the actual integral log-shell

IUT III, Proposition 3.9, (i) (p. 115): the p_v-adic log-volume on the local
holomorphic packets is normalized so that multiplication by p_v corresponds to
adding -log(p_v); IUT III, Proposition 1.2, (iii) (p. 31), states the
compatibility of the log-link with log-volumes.  For the actual integral
log-shell I_v = (p*_v)^-1 * log_v(O^x) of an actual finite-dimensional
p-adic local field K, this file proves the actual measure-theoretic form:

  log mu(p . I_v) = log mu(I_v) - [K : Q_p] * log p,

and the same for the actual integers O_K.  Combining with the actual Haar index
formula log mu(I_v) = log mu(O_K) + logShellIntegerIndex (proved in
IntegralLogShellHaarIndex) gives the exact packet-normalization identity
relating the shell's log-volume to the integral log-volume and the actual
integer index.  For [K : Q_p] = 1 the shift is exactly -log p, the paper's
packet normalization; the dimension factor is the normalized-weight factor of
Remark 3.1.1.  No arbitrary carrier, no True/PUnit, no sorry, no axiom.
WRITE-ONLY; no local compile.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137LogShellHaarLogVolumeScalingActual

open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.FinitePadicHaarScaling
open MeasureTheory
open scoped Pointwise

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [ProperSpace K]
  [MeasurableSpace K] [CharZero K] [CompleteSpace K] [BorelSpace K]
  {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K]

/-- The actual local Haar log-volume of a region. -/
noncomputable def localLogVolume (μ : Measure K) (S : Set K) : ℝ :=
  Real.log (μ S).toReal

/-- The actual log-volume of the integral log-shell equals the actual log index
plus the log-volume of the integers. -/
theorem log_measure_integralLogShell_eq (μ : Measure K)
    [Measure.IsAddHaarMeasure μ] :
    Real.log (μ (integralLogShell (K := K) (p := p) : Set K)).toReal =
      integralLogShellDiscrepancy (K := K) (p := p) +
        Real.log (μ (Integers K : Set K)).toReal := by
  rw [integralLogShellDiscrepancy_eq_relativeHaarLog (K := K) (p := p) μ]
  ring

/-- IUT III, Proposition 3.9, (i): multiplying the actual integral log-shell by
p shifts its Haar log-volume by -[K : Q_p] * log p. -/
theorem log_measure_prime_smul_integralLogShell (μ : Measure K)
    [Measure.IsAddHaarMeasure μ] :
    Real.log (μ ((p : ℚ_[p]) •
        (integralLogShell (K := K) (p := p) : Set K))).toReal =
      -((Module.finrank ℚ_[p] K : ℝ) * Real.log (p : ℝ)) +
        Real.log (μ (integralLogShell (K := K) (p := p) : Set K)).toReal := by
  simpa only [neg_mul] using
    log_measure_prime_smul_finiteDimensional (M := K) (p := p) μ
      (measure_integralLogShell_pos_lt_top (K := K) (p := p) μ).1
      (measure_integralLogShell_pos_lt_top (K := K) (p := p) μ).2

/-- The same p-scaling law for the actual integers O_K. -/
theorem log_measure_prime_smul_integers (μ : Measure K)
    [Measure.IsAddHaarMeasure μ] :
    Real.log (μ ((p : ℚ_[p]) • (Integers K : Set K))).toReal =
      -((Module.finrank ℚ_[p] K : ℝ) * Real.log (p : ℝ)) +
        Real.log (μ (Integers K : Set K)).toReal := by
  simpa only [neg_mul] using
    log_measure_prime_smul_finiteDimensional (M := K) (p := p) μ
      (measure_localIntegers_pos_lt_top (K := K) μ).1
      (measure_localIntegers_pos_lt_top (K := K) μ).2

/-- The actual local log-volume (as a function on regions) of the p-scaled
integral log-shell. -/
theorem localLogVolume_prime_smul_integralLogShell (μ : Measure K)
    [Measure.IsAddHaarMeasure μ] :
    localLogVolume (K := K) μ ((p : ℚ_[p]) •
        (integralLogShell (K := K) (p := p) : Set K)) =
      -((Module.finrank ℚ_[p] K : ℝ) * Real.log (p : ℝ)) +
        localLogVolume (K := K) μ (integralLogShell (K := K) (p := p) : Set K) :=
  log_measure_prime_smul_integralLogShell (K := K) (p := p) μ

/-- Combined packet-normalization identity: the log-volume of the p-scaled
integral log-shell is the actual integer log-volume plus the actual shell index
minus the dimension times log p. -/
theorem packetNormalization_log_measure_prime_smul_integralLogShell
    (μ : Measure K) [Measure.IsAddHaarMeasure μ] :
    Real.log (μ ((p : ℚ_[p]) •
        (integralLogShell (K := K) (p := p) : Set K))).toReal =
      -((Module.finrank ℚ_[p] K : ℝ) * Real.log (p : ℝ)) +
        (Real.log (μ (Integers K : Set K)).toReal +
          integralLogShellDiscrepancy (K := K) (p := p)) := by
  rw [log_measure_prime_smul_integralLogShell (K := K) (p := p) μ,
    integralLogShellDiscrepancy_eq_relativeHaarLog (K := K) (p := p) μ]
  ring

/-- In the paper's normalized-weight case [K : Q_p] = 1 the p-scaling shift is
exactly -log p, i.e. the packet normalization of IUT III, Proposition 3.9, (i). -/
theorem localLogVolume_prime_smul_integralLogShell_finrank_one
    (h1 : Module.finrank ℚ_[p] K = 1) (μ : Measure K)
    [Measure.IsAddHaarMeasure μ] :
    localLogVolume (K := K) μ ((p : ℚ_[p]) •
        (integralLogShell (K := K) (p := p) : Set K)) =
      -Real.log (p : ℝ) +
        localLogVolume (K := K) μ (integralLogShell (K := K) (p := p) : Set K) := by
  rw [localLogVolume_prime_smul_integralLogShell (K := K) (p := p) μ, h1]
  ring

end LeanFormal.IUT.XiFPaper.S3137LogShellHaarLogVolumeScalingActual