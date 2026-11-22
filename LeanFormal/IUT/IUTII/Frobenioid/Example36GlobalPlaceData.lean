import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import LeanFormal.IUT.IUTII.Frobenioid.Example36LocalValueData

/-!
# The place-indexed local value data of a number field (IUT III, Example 3.6)

This is the Layer-2 preamble.  A global ideal family of Example 3.6 is a family
of local integral objects indexed by the places of a number field F, with
almost-everywhere standard finite part.  The local objects are encoded through
their value-group coordinates, and the local value data at every place is a
LocalValueData:

* at a finite place v, the additive value group is Z (the v-adic valuation),
  with the nonnegative cone;
* at an archimedean place w, the additive value group is R with coordinate
  -log w(x), with the nonnegative cone.

This file only freezes the place-indexed data and its elementary principal-map
lemmas.  The actual instantiation with the arithmetic valuations of a number
field is a separate file (it needs the FractionalIdeal factorization API); the
global ideal-family category is in Example36GlobalIdealFamily.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open scoped NumberField
open IsDedekindDomain NumberField

/-- The local value data at all places of a number field. -/
structure GlobalPlaceData (F : Type*) [Field F] [NumberField F] where
  /-- The local value data at the finite places. -/
  finiteValue : HeightOneSpectrum (𝓞 F) → LocalValueData F ℤ
  /-- The local value data at the archimedean places. -/
  infiniteValue : NumberField.InfinitePlace F → LocalValueData F ℝ

namespace GlobalPlaceData

variable {F : Type*} [Field F] [NumberField F]
variable (D : GlobalPlaceData F)

/-- The principal finite-place value coordinate of a global unit. -/
def finiteDelta (f : Fˣ) (v : HeightOneSpectrum (𝓞 F)) : ℤ :=
  (D.finiteValue v).deltaAdd f

/-- The principal archimedean value coordinate of a global unit. -/
def infiniteDelta (f : Fˣ) (w : NumberField.InfinitePlace F) : ℝ :=
  (D.infiniteValue w).deltaAdd f

@[simp]
theorem finiteDelta_one (v : HeightOneSpectrum (𝓞 F)) : D.finiteDelta 1 v = 0 := by
  simp [finiteDelta]

@[simp]
theorem infiniteDelta_one (w : NumberField.InfinitePlace F) : D.infiniteDelta 1 w = 0 := by
  simp [infiniteDelta]

theorem finiteDelta_mul (f g : Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    D.finiteDelta (f * g) v = D.finiteDelta f v + D.finiteDelta g v := by
  simp [finiteDelta]

theorem infiniteDelta_mul (f g : Fˣ) (w : NumberField.InfinitePlace F) :
    D.infiniteDelta (f * g) w = D.infiniteDelta f w + D.infiniteDelta g w := by
  simp [infiniteDelta]

theorem finiteDelta_pow (f : Fˣ) (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    D.finiteDelta (f ^ n) v = n • D.finiteDelta f v := by
  simp only [finiteDelta]
  exact LocalValueData.deltaAdd_pow (D.finiteValue v) f n

theorem infiniteDelta_pow (f : Fˣ) (n : ℕ) (w : NumberField.InfinitePlace F) :
    D.infiniteDelta (f ^ n) w = n • D.infiniteDelta f w := by
  simp only [infiniteDelta]
  exact LocalValueData.deltaAdd_pow (D.infiniteValue w) f n

/-- The finiteness of the finite-place support of a principal divisor is part
of the arithmetic input; it is proved for the actual number-field data in
Example36NumberFieldPlaceData. -/
def HasFiniteSupport (D : GlobalPlaceData F) : Prop :=
  ∀ f : Fˣ, Set.Finite {v : HeightOneSpectrum (𝓞 F) | D.finiteDelta f v ≠ 0}

end GlobalPlaceData

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
