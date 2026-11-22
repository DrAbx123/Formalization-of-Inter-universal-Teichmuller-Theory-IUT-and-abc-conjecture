import tmp.sheaf.xif.paper.Mzk1P0LPaperInstanceActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LReadoutInstanceActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
abbrev qRead : Real := qReadActual I place
abbrev thetaRead : Real := thetaReadActual I place
theorem qRead_eq : qRead I place = -|Real.log ‖(C3LAt I place).q.q‖| := qReadActual_eq I place
theorem qRead_nonpos : qRead I place ≤ 0 := qReadActual_nonpos I place
theorem thetaRead_eq_rawHaar : thetaRead I place =
    Real.log ((actualC3LogShellTensorHaarL (C3LAt I place))
      (actualC3LogShellTensorRegionL (C3LAt I place))).toReal := thetaReadActual_eq_rawHaar I place
end LeanFormal.IUT.XiFPaper.Mzk1P0LReadoutInstanceActual