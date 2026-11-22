import tmp.sheaf.xif.paper.Mzk1P0LPaperInstanceActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LThetaMeasureReadActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open MeasureTheory
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
theorem thetaReadActual_eq_logMeasure :
    thetaReadActual I place =
      Real.log ((actualC3LogShellTensorHaarL (C3LAt I place))
        (actualC3LogShellTensorRegionL (C3LAt I place))).toReal := rfl
theorem thetaReadActual_eq_log_measure' :
    thetaReadActual I place =
      Real.log (((actualC3LogShellTensorHaarL (C3LAt I place))
        (actualC3LogShellTensorRegionL (C3LAt I place))).toReal) := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0LThetaMeasureReadActual