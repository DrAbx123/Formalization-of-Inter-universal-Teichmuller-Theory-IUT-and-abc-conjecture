import LeanFormal.IUT.IUTII.Frobenioid.Example36NumberFieldPlaceData
import LeanFormal.IUT.IUTII.Frobenioid.Example36LocalIdealValuation

/-!
# Global finite-place principal values versus local completion values

IUT III Example 3.6 identifies the finite-place principal value of a global
unit with the value of its image in the local completion.  The global finite
coordinate must therefore be the classical valuation exponent `ν_v(f)` (the
exponent in which integral elements are nonnegative), not its negative.

This file records the bridge and the sign convention:

* `numberFieldGlobalPlaceData_finiteDelta_eq_completionValuationExponent`:
  the global finite coordinate of `numberFieldGlobalPlaceData` equals the
  classical completion exponent `completionValuationExponent` of the embedded
  unit in `v.adicCompletion F`;
* `numberFieldFiniteLocalInclusion_standard_iff`: at the standard object
  (coordinates `0`), the local inclusion condition of the packaged global
  data holds exactly when the classical exponent is nonnegative, i.e. exactly
  when the global unit is integral at `v`;
* `numberFieldFiniteLocalInclusion_standard_of_neg`: a unit with negative
  classical exponent is rejected at the standard object.

As a concrete regression instance of the second point: for `F = ℚ`, `v = (2)`
and `f = 1/2`, the classical exponent is `-1`, so the standard arrow
would mean `(1/2) ℤ_2 ⊆ ℤ_2`, which is false; the local inclusion condition
now rejects it.

Boundary: this is the finite-place global/local sign bridge only; no
archimedean statement, no Hodge theater, no theta-pilot or q-pilot claim.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open IsDedekindDomain NumberField
open scoped NumberField

variable {F : Type*} [Field F] [NumberField F]

/-- **Global finite value equals local completion exponent.**  The finite
coordinate of the actual number-field place data at a finite place `v` is the
classical valuation exponent of the embedded unit in the actual `v`-adic
completion. -/
theorem numberFieldGlobalPlaceData_finiteDelta_eq_completionValuationExponent
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (numberFieldGlobalPlaceData (F := F)).finiteDelta f v =
      completionValuationExponent v
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom f) := by
  rw [numberFieldGlobalPlaceData_finiteDelta, finitePlaceValueExponent,
    completionValuationExponent_coe]

/-- At the standard finite object (coordinates `0`), the local inclusion
condition of the packaged global data holds exactly when the classical
valuation exponent is nonnegative. -/
theorem numberFieldFiniteLocalInclusion_standard_iff
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (f : Fˣ) :
    (numberFieldFiniteLocalValueData v).localInclusion n f 0 0 ↔
      0 ≤ finitePlaceValueExponent v f := by
  rw [numberFieldFiniteLocalInclusion_iff]
  constructor
  · intro h
    simpa using h
  · intro h
    simpa using h

/-- A global unit with negative classical exponent is rejected at the standard
finite object: the corresponding standard arrow would not be integral. -/
theorem numberFieldFiniteLocalInclusion_standard_of_neg
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (f : Fˣ)
    (h : finitePlaceValueExponent v f < 0) :
    ¬(numberFieldFiniteLocalValueData v).localInclusion n f 0 0 := by
  rw [numberFieldFiniteLocalInclusion_standard_iff]
  exact not_le.mpr h

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
