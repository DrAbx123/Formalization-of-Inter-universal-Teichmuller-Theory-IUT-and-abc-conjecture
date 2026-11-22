import tmp.sheaf.xif.paper.Mzk1P0LQThetaMemActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LQThetaMemFinalActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0LQThetaMemActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
def qComponentGapFinal : Prop := qComponentMemGap I place
theorem tensorUnit_mem_of_qComponent_final
    (h : qComponentGapFinal I place) :
    (↑(C3LAt I place).tensorUnit : C3LogShellTensorBlockL (C3LAt I place)) ∈
      actualC3LogShellTensorRegionL (C3LAt I place) :=
  tensorUnit_mem_thetaRegion_of_qComponentMem I place h
end LeanFormal.IUT.XiFPaper.Mzk1P0LQThetaMemFinalActual