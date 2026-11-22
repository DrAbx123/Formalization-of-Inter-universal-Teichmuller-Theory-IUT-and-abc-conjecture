import tmp.sheaf.xif.paper.Mzk1P0LPaperInstanceActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LQThetaArrowActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
abbrev Arrow := LQThetaSourceArrow I place
def ArrowMissing : Prop := LQThetaSourceArrowMissing I place
theorem arrow_missing_iff : ArrowMissing I place ↔ Nonempty (Arrow I place) := Iff.rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0LQThetaArrowActual