import tmp.sheaf.xif.paper.RelativeNormCompletion
import PadicField.FieldNorm
import tmp.sheaf.xif.paper.Mzk1PadicFieldValuedBridgeActual
import tmp.sheaf.xif.paper.Mzk1PadicFieldValuedQpActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceRelativeCommonPrime

noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 2000000
open scoped WithZero
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.RelativeNormCompletion
open LeanFormal.IUT.XiFPaper.Mzk1PadicFieldValuedBridgeActual

namespace LeanFormal.IUT.XiFPaper.RelativeNormFieldNormActual

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The upper rational prime as a Nat.Primes value. -/
abbrev qPlace : Nat.Primes := completionRationalPrime (nativeFPlaceOverBad X)

/-- The comap rational prime as a Nat.Primes value. -/
abbrev qBase : Nat.Primes :=
  completionRationalPrime (comap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X))

/-- The rational prime value used for the scalar field. -/
abbrev pBase : ℕ := (qBase (X := X)).val

local instance instFactPrimes (q : Nat.Primes) : Fact q.val.Prime := ⟨q.2⟩

local instance instBaseAlgebra :
    Algebra ℚ_[pBase (X := X)] (NativeBaseCompletionRaw (X := X)) :=
  padicCompletionAlgebra (comap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X))

local instance instBaseFinite :
    FiniteDimensional ℚ_[pBase (X := X)] (NativeBaseCompletionRaw (X := X)) :=
  moduleFinite_padicCompletionAlgebra
    (comap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X))

local instance instKLAlgebra :
    Algebra (NativeBaseCompletionRaw (X := X)) (NativeFCompletion (X := X)) :=
  relativeCompletionAlgebra (X := X)

variable [Algebra ℚ_[pBase (X := X)] (NativeFCompletion (X := X))]
variable [FiniteDimensional ℚ_[pBase (X := X)] (NativeFCompletion (X := X))]

/-- The spectral-norm norm formula for the actual relative norm. -/
theorem relativeNormRaw_nrm
    (hTower : IsScalarTower ℚ_[pBase (X := X)]
      (NativeBaseCompletionRaw (X := X)) (NativeFCompletion (X := X)))
    (x : NativeFCompletion (X := X)) :
    PadicField.nrm (pBase (X := X)) (NativeBaseCompletionRaw (X := X))
        (relativeNormRaw (X := X) x) =
      PadicField.nrm (pBase (X := X)) (NativeFCompletion (X := X)) x ^
        Module.finrank (NativeBaseCompletionRaw (X := X)) (NativeFCompletion (X := X)) := by
  haveI : IsScalarTower ℚ_[pBase (X := X)]
      (NativeBaseCompletionRaw (X := X)) (NativeFCompletion (X := X)) := hTower
  exact PadicField.nrm_norm (p := pBase (X := X)) x

/-- The contraction of the relative norm, in spectral-norm form. -/
theorem relativeNormRaw_nrm_lt_one
    (hTower : IsScalarTower ℚ_[pBase (X := X)]
      (NativeBaseCompletionRaw (X := X)) (NativeFCompletion (X := X)))
    (hL : PadicValuedCoherence (p := pBase (X := X))
      (K := NativeFCompletion (X := X)))
    (hfr : 0 < Module.finrank (NativeBaseCompletionRaw (X := X)) (NativeFCompletion (X := X)))
    {x : NativeFCompletion (X := X)} (hx : x ≠ 0)
    (hval : (Valued.v x : WithZero (Multiplicative ℤ)) < 1) :
    PadicField.nrm (pBase (X := X)) (NativeBaseCompletionRaw (X := X))
        (relativeNormRaw (X := X) x) < 1 := by
  rw [relativeNormRaw_nrm (X := X) hTower x]
  have hvpos : 0 < PadicField.v (pBase (X := X)) x :=
    (valued_lt_one_iff_padicField_v_neg hL hx).mp hval
  have hlt : PadicField.nrm (pBase (X := X)) (NativeFCompletion (X := X)) x < 1 :=
    (PadicField.nrm_lt_one_iff_v_pos (p := pBase (X := X)) hx).mpr hvpos
  exact pow_lt_one₀ (PadicField.nrm_nonneg (p := pBase (X := X)) x) hlt
    (Nat.ne_of_gt hfr)

/-- The RelativeNorm contraction in the Valued.v form, via the spectral-norm
step and the base coherence. -/
theorem relativeNormRaw_valued_lt_one_via_nrm
    (hTower : IsScalarTower ℚ_[pBase (X := X)]
      (NativeBaseCompletionRaw (X := X)) (NativeFCompletion (X := X)))
    (hK : PadicValuedCoherence (p := pBase (X := X))
      (K := NativeBaseCompletionRaw (X := X)))
    (hL : PadicValuedCoherence (p := pBase (X := X))
      (K := NativeFCompletion (X := X)))
    (hfr : 0 < Module.finrank (NativeBaseCompletionRaw (X := X)) (NativeFCompletion (X := X)))
    (hKL : Module.Finite (NativeBaseCompletionRaw (X := X)) (NativeFCompletion (X := X)))
    {x : NativeFCompletion (X := X)} (hx : x ≠ 0)
    (hval : (Valued.v x : WithZero (Multiplicative ℤ)) < 1) :
    (Valued.v (relativeNormRaw (X := X) x) : WithZero (Multiplicative ℤ)) < 1 := by
  letI : Module.Finite (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X)) := hKL
  have hN : relativeNormRaw (X := X) x ≠ 0 := by
    simpa [relativeNormRaw] using
      (Algebra.norm_ne_zero_iff.mpr hx :
        Algebra.norm (NativeBaseCompletionRaw (X := X)) x ≠ 0)
  rw [valued_lt_one_iff_padicField_v_neg hK hN]
  rw [← PadicField.nrm_lt_one_iff_v_pos (p := pBase (X := X)) hN]
  exact relativeNormRaw_nrm_lt_one (X := X) hTower hL hfr hx hval

end LeanFormal.IUT.XiFPaper.RelativeNormFieldNormActual
