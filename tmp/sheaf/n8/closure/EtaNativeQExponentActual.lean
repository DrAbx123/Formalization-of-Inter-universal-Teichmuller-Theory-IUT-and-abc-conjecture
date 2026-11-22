import tmp.sheaf.n8.closure.EtaQCalibrationBridgeAttempt
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

/-!
# ETA native q exponent actual attempt

Actual identity: the native q-pilot scalar is minus its local order times the
logarithm of the actual residue norm base.  The remaining input for the
p-power exponent is the actual base relation
`residueNormBase base = p ^ f`; production has the relative-residue-degree
relation for the upper place but the base p-power relation is recorded as the
exact gap.  No arbitrary exponent is chosen.
-/

noncomputable section

open MeasureTheory BigOperators
open IsDedekindDomain NumberField
open scoped NumberField
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange

namespace LeanFormal.IUT.N8Closure.EtaNativeQExponentActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual q-pilot scalar equals minus the discrete order times the log of the
actual residue norm base. -/
theorem qPilotSignedLog_eq_order_mul_log :
    qPilotSignedLog X =
      -((C9QPilotRegion.nativeQ X).order : ℝ) * Real.log (residueNormBase (nativeFPlaceOverBad X)) := by
  unfold qPilotSignedLog
  have h := localLogMagnitude_eq_order_mul_log (parameter := C9QPilotRegion.nativeQ X)
  unfold localLogMagnitude at h
  linarith

/-- The rational prime under the native bad base finite place. -/
noncomputable def nativeQBasePrime : ℕ :=
  (NumberFieldFinitePlace.completionRationalPrime
    (nativeBadBasePlace X)).val

theorem nativeQBasePrime_prime : Nat.Prime (nativeQBasePrime X) :=
  (NumberFieldFinitePlace.completionRationalPrime
    (nativeBadBasePlace X)).property

/-- Exact base-power target: the actual base residue norm is the rational
prime raised to the base residue degree. -/
def BaseResidueNormPowerTarget : Prop :=
  ∃ f : ℕ,
    residueNormBase (nativeBadBasePlace X) = (nativeQBasePrime X : ℝ) ^ f

/-- Actual upper/base residue norm relation from production. -/
theorem upper_residueNormBase_eq_base_pow :
    residueNormBase (nativeFPlaceOverBad X) =
      residueNormBase (nativeBadBasePlace X) ^
        localResidueDegree (k := X.S.arithmetic.Fmod)
          (nativeFPlaceOverBad X) := by
  rw [← NativeC3.nativeFPlaceOverBad_comap X]
  exact residueNormBase_eq_lower_pow (k := X.S.arithmetic.Fmod)
    (nativeFPlaceOverBad X)

/-- Conditional native q calibration exponent from the exact base-power
target.  The exponent is the actual product `order * f_upper * f_base`, with
the sign supplied by the q-log. -/
theorem nativeQCalibrationExponent_of_basePower
    (hbase : BaseResidueNormPowerTarget (X := X)) :
    ∃ k : ℤ,
      qPilotSignedLog X = -((k : ℝ) * Real.log (nativeQBasePrime X : ℝ)) := by
  rcases hbase with ⟨fbase, hfbase⟩
  let fupper : ℕ :=
    localResidueDegree (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X)
  let k : ℤ := ((C9QPilotRegion.nativeQ X).order : ℤ) * (fupper * fbase : ℕ)
  refine ⟨k, ?_⟩
  rw [qPilotSignedLog_eq_order_mul_log (X := X),
    upper_residueNormBase_eq_base_pow (X := X), hfbase, Real.log_pow]
  have hupper : 0 < fupper := by
    simpa [fupper] using
      localResidueDegree_pos (k := X.S.arithmetic.Fmod)
        (nativeFPlaceOverBad X)
  have hfbase_pos : 0 < fbase := by
    by_contra h
    have hzero : fbase = 0 := Nat.eq_zero_of_not_pos h
    rw [hzero, pow_zero] at hfbase
    exact (ne_of_gt (residueNormBase_gt_one (nativeBadBasePlace X))) hfbase
  have hk : (k : ℝ) = ((C9QPilotRegion.nativeQ X).order : ℝ) * ((fupper * fbase : ℕ) : ℝ) := by
    simp [k, Int.cast_mul, Int.cast_natCast]
  rw [hk, Nat.cast_mul, Real.log_pow]
  ring

end LeanFormal.IUT.N8Closure.EtaNativeQExponentActual

end