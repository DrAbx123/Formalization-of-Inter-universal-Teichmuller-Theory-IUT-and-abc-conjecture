import tmp.sheaf.xif.paper.S1267TensorUnitActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1219ConcreteTensorLandingActual
open LeanFormal.IUT.XiFPaper.S1267TensorUnitActual
open LeanFormal.IUT.NumberFieldFinitePlace

noncomputable section
universe upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

#print axioms LeanFormal.IUT.XiFPaper.S1267TensorUnitActual.concreteTensorLanding_mul
#print axioms LeanFormal.IUT.XiFPaper.S1267TensorUnitActual.concreteTensorLanding_one
#print axioms LeanFormal.IUT.XiFPaper.S1267TensorUnitActual.concreteTensorUnitOfNeZero
#print axioms LeanFormal.IUT.XiFPaper.S1267TensorUnitActual.concreteTensorUnit
#print axioms LeanFormal.IUT.XiFPaper.S1267TensorUnitActual.concreteTensorLanding_isUnit_via_fieldProduct
#print axioms LeanFormal.IUT.XiFPaper.S1267TensorUnitActual.concreteTensorUnitViaFieldProduct_eq
#print axioms LeanFormal.IUT.XiFPaper.S1267TensorUnitActual.concreteActualTensorUnit

end
