import tmp.sheaf.xif.paper.Mzk1P0LQThetaComponentActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LNormCompatActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0LQThetaComponentActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
def normInstanceCompatGap : Prop := CommonPrimeNormInstanceCompatRequired I place
end LeanFormal.IUT.XiFPaper.Mzk1P0LNormCompatActual