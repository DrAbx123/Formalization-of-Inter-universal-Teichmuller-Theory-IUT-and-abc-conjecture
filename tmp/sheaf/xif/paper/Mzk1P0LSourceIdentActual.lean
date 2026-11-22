import tmp.sheaf.xif.paper.Mzk1P0LPaperInstanceActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LSourceIdentActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
theorem core_eq :
    sourcePilotRegionLToCore I (C3LAt I place) =
      actualSourcePilotRegionCore (I := I) place :=
  actualSourcePilotRegionDataL_toCore (I := I) place
end LeanFormal.IUT.XiFPaper.Mzk1P0LSourceIdentActual