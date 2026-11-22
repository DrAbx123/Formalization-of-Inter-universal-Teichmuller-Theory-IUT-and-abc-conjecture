import tmp.sheaf.xif.paper.S1267TensorUnitActual
import tmp.sheaf.xif.paper.S1267ConsumerProbe

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1219ConcreteTensorLandingActual
open LeanFormal.IUT.XiFPaper.S1267TensorUnitActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual

noncomputable section
universe upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-- With the one-line fix in the donor file, the exact consumer structure
ConcreteTensorLandingData is filled by the diagonal unit. -/
noncomputable def concreteTensorLandingDataActual :
    LeanFormal.IUT.XiFPaper.S1267ConsumerProbe.ConcreteTensorLandingData (I := I) place where
  tensorIndex := ConcreteIndex
  tensorFintype := inferInstance
  tensorPlaceIndex := ConcretePlaceIndex
  tensorPlaces := concretePlaces (I := I) (p := p) place
  tensorTuple := concreteTuple
  tensorUnit := concreteActualTensorUnit (I := I) (p := p) place
  tensorLanding := concreteTensorLanding (I := I) (p := p) place
  tensorLanding_q := rfl

end
