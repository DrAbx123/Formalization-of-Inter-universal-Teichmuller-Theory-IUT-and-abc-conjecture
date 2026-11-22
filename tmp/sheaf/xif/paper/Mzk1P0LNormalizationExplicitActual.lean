import tmp.sheaf.xif.paper.Mzk1P0LNormalizationActual
import tmp.sheaf.xif.paper.Mzk1P0LReadoutLogActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LNormalizationExplicitActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LNormalizationActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LReadoutLogActual
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
theorem lThetaNormFactor_eq_theta_sub_qRead :
    lThetaNormFactor I place = thetaReadActual I place - qReadActual I place := by
  unfold lThetaNormFactor
  rw [qReadActual_eq_logNorm]
theorem lThetaNormFactor_eq_theta_sub_qRead' :
    lThetaNormFactor I place = thetaReadActual I place - qReadActual I place :=
  lThetaNormFactor_eq_theta_sub_qRead I place
end LeanFormal.IUT.XiFPaper.Mzk1P0LNormalizationExplicitActual