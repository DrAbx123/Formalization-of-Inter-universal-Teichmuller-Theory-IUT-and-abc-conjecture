import tmp.sheaf.xif.paper.Mzk1P0LReadoutLogActual
import tmp.sheaf.xif.paper.Mzk1P0LQReadoutSignActual
import tmp.sheaf.xif.paper.Mzk1P0LNormalizationActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LNormalizationSignActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LNormalizationActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LReadoutLogActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LQReadoutSignActual
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
theorem lThetaNormFactor_eq_theta_sub_logNorm :
    lThetaNormFactor I place =
      thetaReadActual I place - Real.log ‖(C3LAt I place).q.q‖ := by
  unfold lThetaNormFactor
  rfl
theorem neg_qReadActual_le_lThetaNormFactor_of_theta_nonneg
    (h : 0 ≤ thetaReadActual I place) :
    -qReadActual I place ≤ lThetaNormFactor I place := by
  rw [lThetaNormFactor_eq_theta_sub_logNorm, qReadActual_eq_logNorm]
  linarith
end LeanFormal.IUT.XiFPaper.Mzk1P0LNormalizationSignActual