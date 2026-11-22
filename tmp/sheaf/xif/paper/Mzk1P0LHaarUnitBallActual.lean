import tmp.sheaf.xif.paper.Mzk1C3S1902UnitMassCitizenActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LHaarUnitBallActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1C3S1902UnitMassCitizenActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
def unitMassOneGap : Prop := actualUnitMass (T := T) = 1
end LeanFormal.IUT.XiFPaper.Mzk1P0LHaarUnitBallActual