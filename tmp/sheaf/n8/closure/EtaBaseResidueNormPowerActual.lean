import tmp.sheaf.n8.closure.EtaNativeQExponentActual
import Mathlib.NumberTheory.RamificationInertia.Inertia

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# Base residue norm power actual attempt

Reduces `BaseResidueNormPowerTarget` to the exact `LiesOver` statement for the
native base maximal ideal over the rational prime.  Under that statement the
production `Ideal.absNorm_eq_pow_inertiaDeg'` gives the p-power with
exponent the actual inertia degree.  Production does not package the base
`LiesOver` instance for the native bad base place; that is the exact gap.

No arbitrary exponent is chosen.
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
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.N8Closure.EtaBaseResidueNormPowerActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Exact base `LiesOver` statement: the native bad base maximal ideal lies over
the rational prime span.  This is the missing base-instance datum. -/
def BaseLiesOverTarget : Prop :=
  (nativeBadBasePlace X).maximalIdeal.asIdeal.LiesOver
    (Ideal.span {((nativeQBasePrime X) : ℤ)})

/-- Under the exact base `LiesOver` statement, the base residue norm is the
rational prime raised to the actual inertia degree. -/
theorem baseResidueNormPower_of_liesOver
    (h : BaseLiesOverTarget (X := X)) :
    BaseResidueNormPowerTarget (X := X) := by
  let P : Ideal (𝓞 X.S.arithmetic.Fmod) :=
    (nativeBadBasePlace X).maximalIdeal.asIdeal
  let q : Ideal ℤ := Ideal.span {((nativeQBasePrime X) : ℤ)}
  letI : P.LiesOver q := h
  refine ⟨q.inertiaDeg' P, ?_⟩
  have hp : Nat.Prime (nativeQBasePrime X) :=
    nativeQBasePrime_prime (X := X)
  have habs : Ideal.absNorm P =
      (nativeQBasePrime X) ^ (q.inertiaDeg' P) :=
    Ideal.absNorm_eq_pow_inertiaDeg' P hp
  have habs_real : (Ideal.absNorm P : ℝ) =
      ((nativeQBasePrime X : ℝ)) ^ (q.inertiaDeg' P) := by
    exact_mod_cast habs
  simpa [BaseResidueNormPowerTarget, ArithmeticQPilotBaseChange.residueNormBase,
    P, q] using habs_real

end LeanFormal.IUT.N8Closure.EtaBaseResidueNormPowerActual

end
