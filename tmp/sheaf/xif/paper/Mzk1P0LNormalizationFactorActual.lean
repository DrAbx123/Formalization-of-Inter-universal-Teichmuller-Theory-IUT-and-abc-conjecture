import tmp.sheaf.xif.paper.Mzk1P0LNormalizationActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LNormalizationFactorActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0LNormalizationActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
noncomputable def explicitNormFactor : Real := lThetaNormFactor I place
theorem explicitNormFactor_eq : explicitNormFactor I place = lThetaNormFactor I place := rfl
def normalizationEqGap : Prop := lThetaNormalizationGap I place
end LeanFormal.IUT.XiFPaper.Mzk1P0LNormalizationFactorActual