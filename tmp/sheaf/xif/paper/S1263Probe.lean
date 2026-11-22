import tmp.sheaf.xif.paper.S1219ConcreteTensorLandingActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1219ConcreteTensorLandingActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
universe upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
#synth Monoid (ConcreteBlock I place)
#synth GroupWithZero (ConcreteBlock I place)
#synth Field (ConcreteBlock I place)
#check (1 : ConcreteBlock I place)
