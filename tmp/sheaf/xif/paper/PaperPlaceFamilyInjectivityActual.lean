import tmp.sheaf.xif.paper.PaperC3TensorBlockActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Place-family injectivity for the nondegenerate C3 tensor block

The source geometry carries an actual place map

  G.place : V -> FinitePlaceAtPrime K p.

The nondegenerate tensor block uses exactly this indexed place family. Its
injectivity is not a field of CompletionValuedSourceGeometry, so it is isolated
here as the exact actual condition:

  PlaceFamilyInjective G := Function.Injective G.place.

Under this condition the tensor place family and the paper place comparison are
injective. No injectivity is fabricated for an arbitrary G.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.PaperPlaceFamilyInjectivityActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual

universe u ua uv upi umon ui

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {l : PrimeGeFive}
variable {V : Type uv} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- The actual injectivity condition for the source place family. -/
def PlaceFamilyInjective : Prop :=
  Function.Injective G.place

/-- The tensor place family is injective under the source place injectivity. -/
theorem paperTensorPlaces_injective
    (h : PlaceFamilyInjective G) :
    Function.Injective (fun v : V => paperTensorPlaces (G := G) v ()) := by
  intro v w hvw
  exact h hvw

/-- The paper place comparison's strip place is injective under the source place
injectivity. -/
theorem paperPlaceComparison_stripPlace_injective
    (h : PlaceFamilyInjective G) :
    Function.Injective (paperPlaceComparison (G := G)).stripPlace := by
  intro v w hvw
  exact h (by simpa [paperPlaceComparison] using hvw)

/-- Under place-family injectivity, equality of tensor places is exactly
equality of source indices. -/
theorem paperTensorPlaces_eq_iff
    (h : PlaceFamilyInjective G) (v w : V) :
    paperTensorPlaces (G := G) v () = paperTensorPlaces (G := G) w () ↔ v = w := by
  constructor
  · intro hvw
    exact paperTensorPlaces_injective G h hvw
  · rintro rfl
    rfl

/-- Under place-family injectivity, equality of the paper comparison strip
places is exactly equality of source indices. -/
theorem paperPlaceComparison_stripPlace_eq_iff
    (h : PlaceFamilyInjective G) (v w : V) :
    (paperPlaceComparison (G := G)).stripPlace v =
      (paperPlaceComparison (G := G)).stripPlace w ↔ v = w := by
  constructor
  · intro hvw
    exact paperPlaceComparison_stripPlace_injective G h hvw
  · rintro rfl
    rfl

/-- Actual injectivity data for the place family. -/
structure PlaceFamilyInjectiveData where
  injective : PlaceFamilyInjective G

/-- The exact missing condition: the source place family is not known to be
injective from the bare CompletionValuedSourceGeometry fields. -/
def PlaceFamilyInjectiveRequired : Prop :=
  Nonempty (PlaceFamilyInjectiveData G)

/-- The exact failure condition for injectivity. -/
def PlaceFamilyNoninjectiveObstruction : Prop :=
  ¬ PlaceFamilyInjective G

/-- Conditional tensor-place injectivity from actual injectivity data. -/
theorem paperTensorPlaces_injective_of_data
    (D : PlaceFamilyInjectiveData G) :
    Function.Injective (fun v : V => paperTensorPlaces (G := G) v ()) :=
  paperTensorPlaces_injective G D.injective

end LeanFormal.IUT.XiFPaper.PaperPlaceFamilyInjectivityActual

end
