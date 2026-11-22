import tmp.sheaf.xif.paper.Mzk1P0LQReadoutSignActual
import tmp.sheaf.xif.paper.Mzk1P0LQThetaStrictActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LQThetaJointSignActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LQReadoutSignActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LQThetaStrictActual
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
theorem qReadActual_lt_theta_of_theta_nonneg
    (h : 0 ≤ thetaReadActual I place) :
    qReadActual I place < thetaReadActual I place := by
  have hq : qReadActual I place < 0 := qReadActual_neg I place
  linarith
theorem qReadActual_le_theta_of_theta_nonneg
    (h : 0 ≤ thetaReadActual I place) :
    qReadActual I place ≤ thetaReadActual I place :=
  (qReadActual_lt_theta_of_theta_nonneg I place h).le
end LeanFormal.IUT.XiFPaper.Mzk1P0LQThetaJointSignActual