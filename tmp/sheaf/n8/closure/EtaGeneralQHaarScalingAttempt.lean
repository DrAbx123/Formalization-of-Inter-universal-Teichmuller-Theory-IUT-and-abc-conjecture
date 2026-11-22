import tmp.sheaf.n8.closure.EtaQRegionHaarCalibrationActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling

/-!
# EtaGeneralQHaarScalingAttempt

Attempt to derive the corrected qO Haar scaling

  mu(qO) = ofReal (||q||^f) * mu(O)

from the production rational-prime scaling theorem plus unit/translation
invariance.

What production supplies is only

  `FinitePadicHaarScaling.measure_prime_smul_finiteDimensional`,

i.e. scaling by the rational prime `p` on a finite-dimensional Q_p space, with
factor `p^(-finrank)`.  That gives integer p-power scalings, but not scaling by
an arbitrary uniformizer (or by q): for a ramified extension the uniformizer
exponent e is the e-th root of the p-step, and the norm-one unit part is not
covered by a production Haar-invariance theorem.

Therefore the corrected calibration remains the exact missing theorem below.
No arbitrary factor or measure equality is assumed.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingAttempt

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaQRegionHaarCalibrationActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open MeasureTheory
open scoped NumberField ENNReal Pointwise

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The exact general-q scaling target, restated from the corrected calibration. -/
abbrev EtaGeneralQHaarScalingTarget
    (μ : Measure (QCompletion X))
    [Measure.IsAddHaarMeasure μ] : Prop :=
  EtaQRegionHaarCalibrationCorrected X μ

/-- The production p-scaling factor, recorded as the only available Haar
scaling datum.  It is the rational-prime step, not the general q factor. -/
theorem production_pScaling_factor_available
    (p : ℕ) [Fact (Nat.Prime p)]
    (M : Type*) [NormedAddCommGroup M] [NormedSpace ℚ_[p] M]
    [FiniteDimensional ℚ_[p] M] [MeasurableSpace M] [BorelSpace M]
    (ν : Measure M) [Measure.IsAddHaarMeasure ν] (S : Set M) :
    ν ((p : ℚ_[p]) • S) =
      ((p : ENNReal) ^ Module.finrank ℚ_[p] M)⁻¹ * ν S :=
  LeanFormal.IUT.FinitePadicHaarScaling.measure_prime_smul_finiteDimensional
    (p := p) (M := M) ν S

end LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingAttempt