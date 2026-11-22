import tmp.sheaf.n8.closure.EtaQOClassReadoutNormalizedActual
import tmp.sheaf.n8.closure.EtaQRegionRepresentation

/-!
# Eta F-place log-norm agreement actual

Target: Real.log ||nativeQUnitKf|| = qPilotSignedLog.

Actual reduction: it suffices that the normalized F-completion norm of the
transported native q unit equals the native completion norm of q:

  ||nativeQUnitKf|| = ||(nativeQ X).q||.

The remaining equality is the normalized/native norm comparison.  Production
has the unit-ball comparison normalizedCompletion_norm_le_one_iff, but no exact
norm equality theorem for arbitrary elements; that is the exact dependency.
No arbitrary norm normalization is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaFPlaceLogNormAgreementActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaQOClassReadoutNormalizedActual
open LeanFormal.IUT.N8Closure.EtaQORegionMassNormFromScaling
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open ABCBridge.N8.C3TensorTargetCorrection

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Exact normalized/native norm agreement for the transported q unit. -/
def FPlaceNormAgreement : Prop :=
  ‖((nativeQUnitKf X) : KfX X)‖ = ‖(C9QPilotRegion.nativeQ X).q‖

/-- Actual reduction: norm agreement gives the F-place log-norm agreement. -/
theorem fPlaceLogNormAgreement_of_normAgreement
    (h : FPlaceNormAgreement X) :
    FPlaceLogNormAgreement X := by
  rw [FPlaceLogNormAgreement, h]
  calc
    Real.log ‖(C9QPilotRegion.nativeQ X).q‖ = qORegionLogVolume X := rfl
    _ = qPilotKummerRelativeVolume X :=
      qORegionLogVolume_eq_qPilotKummer X
    _ = qPilotSignedLog X := qPilotKummerRelativeVolume_eq X

end LeanFormal.IUT.N8Closure.EtaFPlaceLogNormAgreementActual
