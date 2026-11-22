import tmp.sheaf.xif.paper.Mzk1P0LPaperInstanceActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LSignedLogActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1S3137LReadoutActual
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
noncomputable def thetaSignedActual : Real := -thetaReadActual I place
theorem thetaSignedActual_eq :
    thetaSignedActual I place = -thetaReadActual I place := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0LSignedLogActual