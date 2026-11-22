import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceLogShell

/-!
# Actual completions with one common rational prime

The place is actual number-field data and its prime equality is explicit.
An independent alias transports the already proved normalized-completion
structures to the common Qp scalar, without changing the actual norm.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

abbrev FinitePlaceAtPrime (K : Type*) [Field K] [NumberField K] (p : ℕ) :=
  { place : NumberField.FinitePlace K // (completionRationalPrime place).val = p }

def CommonPrimeCompletion (place : FinitePlaceAtPrime K p) := NormalizedCompletion place.val

instance commonPrimeCompletionField (place : FinitePlaceAtPrime K p) :
    Field (CommonPrimeCompletion place) :=
  inferInstanceAs (Field (NormalizedCompletion place.val))

instance commonPrimeCompletionCharZero (place : FinitePlaceAtPrime K p) :
    CharZero (CommonPrimeCompletion place) :=
  inferInstanceAs (CharZero (NormalizedCompletion place.val))

instance commonPrimeCompletionNormedField (place : FinitePlaceAtPrime K p) :
    NormedField (CommonPrimeCompletion place) :=
  inferInstanceAs (NormedField (NormalizedCompletion place.val))

instance commonPrimeCompletionNormedAlgebra (place : FinitePlaceAtPrime K p) :
    NormedAlgebra ℚ_[p] (CommonPrimeCompletion place) := by
  rcases place with ⟨place, hprime⟩
  cases hprime
  exact normalizedCompletionNormedAlgebra place

instance commonPrimeCompletionAlgebra (place : FinitePlaceAtPrime K p) :
    Algebra ℚ_[p] (CommonPrimeCompletion place) :=
  (commonPrimeCompletionNormedAlgebra place).toAlgebra

instance commonPrimeCompletionFinite (place : FinitePlaceAtPrime K p) :
    FiniteDimensional ℚ_[p] (CommonPrimeCompletion place) := by
  rcases place with ⟨place, hprime⟩
  cases hprime
  exact normalizedCompletionFinite place

instance commonPrimeCompletionUltrametric (place : FinitePlaceAtPrime K p) :
    IsUltrametricDist (CommonPrimeCompletion place) :=
  inferInstanceAs (IsUltrametricDist (NormalizedCompletion place.val))

instance commonPrimeCompletionComplete (place : FinitePlaceAtPrime K p) :
    CompleteSpace (CommonPrimeCompletion place) :=
  inferInstanceAs (CompleteSpace (NormalizedCompletion place.val))

instance commonPrimeCompletionProper (place : FinitePlaceAtPrime K p) :
    ProperSpace (CommonPrimeCompletion place) :=
  inferInstanceAs (ProperSpace (NormalizedCompletion place.val))

def commonPrimeCompletionRingEquiv (place : FinitePlaceAtPrime K p) :
    CommonPrimeCompletion place ≃+* NormalizedCompletion place.val := RingEquiv.refl _

omit [Fact p.Prime] in
theorem isometry_commonPrimeCompletionRingEquiv (place : FinitePlaceAtPrime K p) :
    Isometry (commonPrimeCompletionRingEquiv place) := Isometry.of_dist_eq (fun _ _ => rfl)

omit [Fact p.Prime] in
theorem completionRationalPrime_eq_of_comap_eq
    {first second : NumberField.FinitePlace K}
    (hplace : comap (k := ℚ) first = comap (k := ℚ) second) :
    completionRationalPrime first = completionRationalPrime second := by
  unfold completionRationalPrime
  rw [hplace]

end

end LeanFormal.IUT.NumberFieldFinitePlace
