import tmp.sheaf.xif.paper.Mzk1P0LNormalizationFactorActual
import tmp.sheaf.xif.paper.Mzk1P0LHaarUnitBallActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LNormalizationBridgeActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0LNormalizationFactorActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LHaarUnitBallActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
structure C0NormalizationBridge (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] where
  unitMass : Real
  unitMass_pos : 0 < unitMass
  factor : Real
  factor_eq : factor = lThetaNormFactor I place
  normalization_eq : thetaReadActual I place = Real.log ‖(C3LAt I place).q.q‖ + Real.log unitMass
def C0NormalizationBridgeRequired : Prop := Nonempty (C0NormalizationBridge I place T)
end LeanFormal.IUT.XiFPaper.Mzk1P0LNormalizationBridgeActual