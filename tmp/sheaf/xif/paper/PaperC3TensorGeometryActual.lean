import tmp.sheaf.xif.paper.PaperSourceGeometryActual

/-! # Nondegenerate C3 tensor geometry from actual source places -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperC3TensorGeometryActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual

universe ua uv upi umon ui u

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type uv} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- The actual nondegenerate C3 tensor index: the source place index itself. -/
abbrev PaperTensorIndex : Type uv := V

/-- The tensor place index: one completion factor per source place. -/
abbrev PaperTensorPlaceIndex : PaperTensorIndex (V := V) → Type := fun _ => Unit

/-- The actual tensor places: the source completion place at `v`. -/
def paperTensorPlaces (v : PaperTensorIndex (V := V))
    (_ : PaperTensorPlaceIndex v) : FinitePlaceAtPrime K p :=
  G.place v

/-- The actual tensor tuple. -/
def paperTensorTuple (v : PaperTensorIndex (V := V)) :
    PaperTensorPlaceIndex v := ()

/-- The actual nondegenerate tensor geometry. -/
structure PaperC3TensorGeometry where
  tensorIndex : Type uv
  tensorFintype : Fintype tensorIndex
  tensorPlaceIndex : tensorIndex → Type
  tensorPlaces : (i : tensorIndex) → tensorPlaceIndex i → FinitePlaceAtPrime K p
  tensorTuple : (i : tensorIndex) → tensorPlaceIndex i

noncomputable def paperC3TensorGeometry : PaperC3TensorGeometry (K := K) (p := p) where
  tensorIndex := V
  tensorFintype := inferInstance
  tensorPlaceIndex := fun _ => Unit
  tensorPlaces := fun v _ => G.place v
  tensorTuple := fun _ => ()

/-- The source-place/tensor-place comparison for the new nondegenerate model. -/
structure PaperPlaceComparison where
  indexEquiv : V ≃ V
  stripPlace : V → FinitePlaceAtPrime K p
  stripPlace_eq : ∀ v, stripPlace v = G.place (indexEquiv v)

/-- The actual place comparison: identity index equivalence and the source place. -/
noncomputable def paperPlaceComparison : PaperPlaceComparison (G := G) where
  indexEquiv := Equiv.refl V
  stripPlace := G.place
  stripPlace_eq := fun _ => rfl

theorem paperPlaceComparison_index (v : V) :
    (paperPlaceComparison (G := G)).indexEquiv v = v := rfl

theorem paperPlaceComparison_place (v : V) :
    (paperPlaceComparison (G := G)).stripPlace v = G.place v := rfl

end LeanFormal.IUT.XiFPaper.PaperC3TensorGeometryActual

end
