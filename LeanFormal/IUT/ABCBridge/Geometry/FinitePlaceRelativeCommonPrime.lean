import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion

/-!
# Contraction and an actual section over a common rational prime

Contraction through number-field extensions preserves the rational prime.
Surjectivity of the already proved finite-place contraction then constructs
a genuine selected upper place over each lower place, with a left inverse.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

noncomputable section

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
variable {p : ℕ}

theorem completionRationalPrime_comap (place : NumberField.FinitePlace K) :
    completionRationalPrime (comap (k := k) place) = completionRationalPrime place := by
  unfold completionRationalPrime
  rw [comap_comap]

def relativeCommonPrimePlace (place : FinitePlaceAtPrime K p) : FinitePlaceAtPrime k p :=
  ⟨comap (k := k) place.val, by rw [completionRationalPrime_comap]; exact place.property⟩

theorem relativeCommonPrimePlace_val (place : FinitePlaceAtPrime K p) :
    (relativeCommonPrimePlace (k := k) place).val = comap (k := k) place.val := rfl

theorem relativeCommonPrimePlace_surjective :
    Function.Surjective (relativeCommonPrimePlace (k := k) (K := K) (p := p)) := by
  intro lower
  obtain ⟨upper, hupper⟩ := comap_surjective (k := k) (K := K) lower.val
  have hprime : (completionRationalPrime upper).val = p := by
    rw [← completionRationalPrime_comap (k := k) upper, hupper]
    exact lower.property
  exact ⟨⟨upper, hprime⟩, Subtype.ext hupper⟩

def selectedCommonPrimePlace (lower : FinitePlaceAtPrime k p) : FinitePlaceAtPrime K p :=
  Classical.choose (relativeCommonPrimePlace_surjective (k := k) (K := K) lower)

theorem relativeCommonPrimePlace_selected (lower : FinitePlaceAtPrime k p) :
    relativeCommonPrimePlace (k := k) (selectedCommonPrimePlace (K := K) lower) = lower :=
  Classical.choose_spec (relativeCommonPrimePlace_surjective (k := k) (K := K) lower)

theorem selectedCommonPrimePlace_injective :
    Function.Injective (selectedCommonPrimePlace (k := k) (K := K) (p := p)) :=
  Function.LeftInverse.injective (relativeCommonPrimePlace_selected (k := k) (K := K))

end

end LeanFormal.IUT.NumberFieldFinitePlace
