import tmp.sheaf.xif.paper.RelativeNormQPropertiesActual
import tmp.sheaf.xif.paper.BasePlaceQCandidateActual

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
open LeanFormal.IUT.XiFPaper.RelativeNormQPropertiesActual
open LeanFormal.IUT.XiFPaper.Mzk1PadicFieldValuedBridgeActual
open LeanFormal.IUT.XiFPaper.BasePlaceQCandidateActual

namespace LeanFormal.IUT.XiFPaper.Node09RelativeNormConsumerActual

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance instFactPrimes (q : Nat.Primes) : Fact q.val.Prime := ⟨q.2⟩

local instance instBaseAlgebra :
    Algebra ℚ_[pBase (X := X)] (RelativeNormCompletion.NativeBaseCompletionRaw (X := X)) :=
  padicCompletionAlgebra (comap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X))

local instance instBaseFinite :
    FiniteDimensional ℚ_[pBase (X := X)] (RelativeNormCompletion.NativeBaseCompletionRaw (X := X)) :=
  moduleFinite_padicCompletionAlgebra
    (comap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X))

local instance instKLAlgebra :
    Algebra (RelativeNormCompletion.NativeBaseCompletionRaw (X := X)) (RelativeNormCompletion.NativeFCompletion (X := X)) :=
  relativeCompletionAlgebra (X := X)

variable [Algebra ℚ_[pBase (X := X)] (RelativeNormCompletion.NativeFCompletion (X := X))]
variable [FiniteDimensional ℚ_[pBase (X := X)] (RelativeNormCompletion.NativeFCompletion (X := X))]

/-- Node09 input: the actual RelativeNormQProperties from the clean interface. -/
theorem relativeNormQProperties_actual
    (hTower : IsScalarTower ℚ_[pBase (X := X)]
      (RelativeNormCompletion.NativeBaseCompletionRaw (X := X)) (RelativeNormCompletion.NativeFCompletion (X := X)))
    (hK : PadicValuedCoherence (p := pBase (X := X))
      (K := RelativeNormCompletion.NativeBaseCompletionRaw (X := X)))
    (hL : PadicValuedCoherence (p := pBase (X := X))
      (K := RelativeNormCompletion.NativeFCompletion (X := X)))
    (hfr : 0 < Module.finrank (RelativeNormCompletion.NativeBaseCompletionRaw (X := X)) (RelativeNormCompletion.NativeFCompletion (X := X)))
    (hKL : Module.Finite (RelativeNormCompletion.NativeBaseCompletionRaw (X := X)) (RelativeNormCompletion.NativeFCompletion (X := X)))
    (hqne : RelativeNormCompletion.relativeNormCompletion (X := X) (nativeQActual X).q ≠ 0)
    (hcastval : ∀ y : RelativeNormCompletion.NativeBaseCompletionRaw (X := X),
      (Valued.v (cast (congrArg (fun p : NumberField.FinitePlace X.S.arithmetic.Fmod =>
        NumberFieldFinitePlace.Completion p) (nativeFPlaceOverBad_comap X)) y) :
          WithZero (Multiplicative ℤ)) =
        (Valued.v y : WithZero (Multiplicative ℤ))) :
    RelativeNormQProperties (X := X) :=
  relativeNormQProperties_of_hypotheses (X := X)
    hTower hK hL hfr hKL hqne hcastval

/-- Node09 consumer: the actual base q candidate from the relative norm. -/
noncomputable def baseQCandidate_actual
    (hTower : IsScalarTower ℚ_[pBase (X := X)]
      (RelativeNormCompletion.NativeBaseCompletionRaw (X := X)) (RelativeNormCompletion.NativeFCompletion (X := X)))
    (hK : PadicValuedCoherence (p := pBase (X := X))
      (K := RelativeNormCompletion.NativeBaseCompletionRaw (X := X)))
    (hL : PadicValuedCoherence (p := pBase (X := X))
      (K := RelativeNormCompletion.NativeFCompletion (X := X)))
    (hfr : 0 < Module.finrank (RelativeNormCompletion.NativeBaseCompletionRaw (X := X)) (RelativeNormCompletion.NativeFCompletion (X := X)))
    (hKL : Module.Finite (RelativeNormCompletion.NativeBaseCompletionRaw (X := X)) (RelativeNormCompletion.NativeFCompletion (X := X)))
    (hqne : RelativeNormCompletion.relativeNormCompletion (X := X) (nativeQActual X).q ≠ 0)
    (hcastval : ∀ y : RelativeNormCompletion.NativeBaseCompletionRaw (X := X),
      (Valued.v (cast (congrArg (fun p : NumberField.FinitePlace X.S.arithmetic.Fmod =>
        NumberFieldFinitePlace.Completion p) (nativeFPlaceOverBad_comap X)) y) :
          WithZero (Multiplicative ℤ)) =
        (Valued.v y : WithZero (Multiplicative ℤ))) :
    FinitePlaceQCandidate (nativeBadBasePlace X) :=
  RelativeNormCompletion.baseQCandidateOfRelativeNorm (X := X)
    (relativeNormQProperties_actual (X := X)
      hTower hK hL hfr hKL hqne hcastval)

/-- Node09 consumer: the assembled BasePlaceQCandidateActual.BaseQDescentData with the actual relative norm. -/
noncomputable def baseQDescentData_actual
    (hTower : IsScalarTower ℚ_[pBase (X := X)]
      (RelativeNormCompletion.NativeBaseCompletionRaw (X := X)) (RelativeNormCompletion.NativeFCompletion (X := X)))
    (hK : PadicValuedCoherence (p := pBase (X := X))
      (K := RelativeNormCompletion.NativeBaseCompletionRaw (X := X)))
    (hL : PadicValuedCoherence (p := pBase (X := X))
      (K := RelativeNormCompletion.NativeFCompletion (X := X)))
    (hfr : 0 < Module.finrank (RelativeNormCompletion.NativeBaseCompletionRaw (X := X)) (RelativeNormCompletion.NativeFCompletion (X := X)))
    (hKL : Module.Finite (RelativeNormCompletion.NativeBaseCompletionRaw (X := X)) (RelativeNormCompletion.NativeFCompletion (X := X)))
    (hqne : RelativeNormCompletion.relativeNormCompletion (X := X) (nativeQActual X).q ≠ 0)
    (hcastval : ∀ y : RelativeNormCompletion.NativeBaseCompletionRaw (X := X),
      (Valued.v (cast (congrArg (fun p : NumberField.FinitePlace X.S.arithmetic.Fmod =>
        NumberFieldFinitePlace.Completion p) (nativeFPlaceOverBad_comap X)) y) :
          WithZero (Multiplicative ℤ)) =
        (Valued.v y : WithZero (Multiplicative ℤ))) :
    BasePlaceQCandidateActual.BaseQDescentData (X := X) where
  descent := RelativeNormCompletion.relativeNormCompletion (X := X)
  q_ne_zero := hqne
  valuation_lt_one := (relativeNormQProperties_actual (X := X)
    hTower hK hL hfr hKL hqne hcastval).valuation_lt_one

end LeanFormal.IUT.XiFPaper.Node09RelativeNormConsumerActual
