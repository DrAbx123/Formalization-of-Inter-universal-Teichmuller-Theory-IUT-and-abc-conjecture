import tmp.sheaf.n8.closure.EtaGlobalQONativeNormActual
import Mathlib

/-!
# Eta global qO degree-corrected alignment

The canonical globalQOCarrier is closedBall 0 ||native q||.  The actual qO
region is closedBall 0 ||normalized q||, and the native/normalized relation is

  ||native q|| = ||normalized q|| ^ relDegree.

Therefore the corrected canonical carrier

  correctedGlobalQOCarrier := closedBall 0 (||native q|| ^ (1 / relDegree))

is exactly the actual qO region, using the power relation.  No assumption
relDegree = 1 is made; if relDegree = 0 or the power relation is absent, this is
the exact gap.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaFPlaceNormAgreementActualAttempt
open LeanFormal.IUT.N8Closure.EtaQORegionMassNormFromScaling
open LeanFormal.IUT.N8Closure.EtaKfClosedBallEqQORegion
open LeanFormal.IUT.N8Closure.EtaGlobalQONativeNormActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField

namespace LeanFormal.IUT.N8Closure.EtaGlobalQODegreeCorrectedAlignment

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

/-- Degree-corrected canonical global qO carrier. -/
noncomputable def correctedGlobalQOCarrier : Set (EtaGeneralQHaarScalingActual.Kf X) :=
  Metric.closedBall (0 : EtaGeneralQHaarScalingActual.Kf X)
    (‖nativeQVal X‖ ^ ((relDegree X : ℝ)⁻¹))

/-- Actual alignment of the degree-corrected carrier with the qO region. -/
theorem correctedGlobalQOCarrier_eq_qORegion
    (hpow : NativeNormPowerRelation X)
    (hrel : (relDegree X : ℝ) ≠ 0) :
    correctedGlobalQOCarrier X =
      qORegion X
        ((nativeQUnitKf X) : EtaGeneralQHaarScalingActual.Kf X) := by
  rw [kf_qORegion_eq_closedBall (X := X) (nativeQUnitKf X)]
  unfold correctedGlobalQOCarrier
  congr 1
  rw [hpow]
  exact Real.pow_rpow_inv_natCast (norm_nonneg _)
    (Nat.cast_ne_zero.mp hrel)

/-- Exact gap: the corrected alignment needs the norm power relation and a
nonzero relative degree. -/
structure CorrectedGlobalQOAlignmentGap : Prop where
  powerRelation : NativeNormPowerRelation X
  relDegree_ne_zero : (relDegree X : ℝ) ≠ 0

end LeanFormal.IUT.N8Closure.EtaGlobalQODegreeCorrectedAlignment
