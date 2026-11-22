import tmp.sheaf.n8.closure.EtaBaseResidueNormPowerActual
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# Base LiesOver actual proof

Proves `BaseLiesOverTarget` from the actual base finite place, its rational
prime, and the production `Rat.HeightOneSpectrum` span relation.  Then closes
the base residue norm power target and the native q calibration exponent.
-/

noncomputable section

open MeasureTheory BigOperators
open IsDedekindDomain NumberField
open scoped NumberField
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaNativeQExponentActual
open LeanFormal.IUT.N8Closure.EtaBaseResidueNormPowerActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange

namespace LeanFormal.IUT.N8Closure.EtaBaseLiesOverActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

theorem baseLiesOverTarget_actual :
    BaseLiesOverTarget (X := X) := by
  let place := nativeBadBasePlace X
  let v := (comap (k := ℚ) place).maximalIdeal
  let p : ℕ := nativeQBasePrime X
  have hspan := Rat.HeightOneSpectrum.span_natGenerator v
  have hmem_map : ((p : ℤ) ∈
      v.asIdeal.map (Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ))) := by
    rw [← hspan]
    exact Ideal.mem_span_singleton.mpr dvd_rfl
  have hmem_v : (Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)).symm
      (p : ℤ) ∈ v.asIdeal := by
    rw [Ideal.symm_apply_mem_of_equiv_iff]
    exact hmem_map
  have halg_hom : (algebraMap ℤ (NumberField.RingOfIntegers ℚ) :ℤ →+* NumberField.RingOfIntegers ℚ) =
      (Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)).symm :=
    RingHom.ext_int _ _
  have halg : (algebraMap ℤ (NumberField.RingOfIntegers ℚ)) (p : ℤ) =
      (Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)).symm (p : ℤ) :=
    congrArg (fun f : ℤ →+* NumberField.RingOfIntegers ℚ => f (p : ℤ)) halg_hom
  have hlies := comap_liesOver (k := ℚ) place
  change place.maximalIdeal.asIdeal.LiesOver (Ideal.span {(p : ℤ)})
  rw [Ideal.liesOver_span_iff]
  · rw [IsScalarTower.algebraMap_apply ℤ (NumberField.RingOfIntegers ℚ)
      (NumberField.RingOfIntegers X.S.arithmetic.Fmod)]
    change algebraMap (NumberField.RingOfIntegers ℚ)
      (NumberField.RingOfIntegers X.S.arithmetic.Fmod)
      (algebraMap ℤ (NumberField.RingOfIntegers ℚ) (p : ℤ)) ∈
      place.maximalIdeal.asIdeal
    let x : NumberField.RingOfIntegers ℚ :=
      algebraMap ℤ (NumberField.RingOfIntegers ℚ) (p : ℤ)
    have hx_v : x ∈ v.asIdeal := by
      simpa [x, halg] using hmem_v
    have hx_under : x ∈ Ideal.under (NumberField.RingOfIntegers ℚ)
        place.maximalIdeal.asIdeal := by
      rw [← hlies.over]
      exact hx_v
    have hfx : (algebraMap (NumberField.RingOfIntegers ℚ)
        (NumberField.RingOfIntegers X.S.arithmetic.Fmod)) x =
        (p : NumberField.RingOfIntegers X.S.arithmetic.Fmod) := by
      dsimp [x]
      norm_num
    exact (Ideal.mem_comap).mp (by simpa [Ideal.under_def, hfx] using hx_under)
  · exact place.maximalIdeal.isPrime.ne_top
  · exact Nat.prime_iff_prime_int.mp (nativeQBasePrime_prime (X := X))

theorem baseResidueNormPowerTarget_actual :
    BaseResidueNormPowerTarget (X := X) :=
  baseResidueNormPower_of_liesOver (X := X)
    (baseLiesOverTarget_actual (X := X))

theorem nativeQCalibrationExponent_actual :
    ∃ k : ℤ,
      qPilotSignedLog X =
        -((k : ℝ) * Real.log (nativeQBasePrime X : ℝ)) :=
  nativeQCalibrationExponent_of_basePower (X := X)
    (baseResidueNormPowerTarget_actual (X := X))

end LeanFormal.IUT.N8Closure.EtaBaseLiesOverActual

end