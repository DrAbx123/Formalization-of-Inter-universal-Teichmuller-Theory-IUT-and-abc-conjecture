import tmp.sheaf.xif.paper.RelativeNormFieldNormActual
import tmp.sheaf.xif.paper.RelativeNormCompletion

noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 2000000
open scoped WithZero
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.RelativeNormCompletion
open LeanFormal.IUT.XiFPaper.RelativeNormFieldNormActual
open LeanFormal.IUT.XiFPaper.Mzk1PadicFieldValuedBridgeActual

namespace LeanFormal.IUT.XiFPaper.RelativeNormQPropertiesActual

variable {l : PrimeGeFive} (X : N8NativeInput l)

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

/-- Clean exact interface for the actual RelativeNormQProperties: the raw
relative-norm contraction is supplied by the nrm_norm route; the two remaining
cast/instance inputs are explicit hypotheses. -/
theorem relativeNormQProperties_of_hypotheses
    (hTower : IsScalarTower ℚ_[pBase (X := X)]
      (NativeBaseCompletionRaw (X := X)) (NativeFCompletion (X := X)))
    (hK : PadicValuedCoherence (p := pBase (X := X))
      (K := NativeBaseCompletionRaw (X := X)))
    (hL : PadicValuedCoherence (p := pBase (X := X))
      (K := NativeFCompletion (X := X)))
    (hfr : 0 < Module.finrank (NativeBaseCompletionRaw (X := X)) (NativeFCompletion (X := X)))
    (hKL : Module.Finite (NativeBaseCompletionRaw (X := X)) (NativeFCompletion (X := X)))
    (hqne : relativeNormCompletion (X := X) (nativeQActual X).q ≠ 0)
    (hcastval : ∀ y : NativeBaseCompletionRaw (X := X),
      (Valued.v (cast (congrArg (fun p : NumberField.FinitePlace X.S.arithmetic.Fmod =>
        NumberFieldFinitePlace.Completion p) (nativeFPlaceOverBad_comap X)) y) :
          WithZero (Multiplicative ℤ)) =
        (Valued.v y : WithZero (Multiplicative ℤ))) :
    RelativeNormQProperties (X := X) where
  q_ne_zero := hqne
  valuation_lt_one := by
    have hmain := relativeNormRaw_valued_lt_one_via_nrm (X := X)
      hTower hK hL hfr hKL (nativeQActual X).q_ne_zero (nativeQActual X).valuation_lt_one
    have hcast := hcastval (relativeNormRaw (X := X) (nativeQActual X).q)
    simpa [relativeNormCompletion, hcast] using hmain

end LeanFormal.IUT.XiFPaper.RelativeNormQPropertiesActual
