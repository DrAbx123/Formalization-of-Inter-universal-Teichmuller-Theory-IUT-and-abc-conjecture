import tmp.sheaf.xif.paper.Mzk1P0LPaperInstanceActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LRegionMassActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
theorem regionMass_lt_top :
    actualC3LogShellTensorHaarL (C3LAt I place)
      (actualC3LogShellTensorRegionL (C3LAt I place)) < ⊤ :=
  actualC3LogShellTensorHaarL_lt_top (C3LAt I place)
def regionMassPosGap : Prop :=
  0 < actualC3LogShellTensorHaarL (C3LAt I place)
    (actualC3LogShellTensorRegionL (C3LAt I place))
end LeanFormal.IUT.XiFPaper.Mzk1P0LRegionMassActual