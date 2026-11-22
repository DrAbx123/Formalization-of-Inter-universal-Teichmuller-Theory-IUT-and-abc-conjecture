import tmp.sheaf.xif.paper.Mzk1P0LNormalizationSignActual
import tmp.sheaf.xif.paper.Mzk1P0LNormalizationExplicitActual
import tmp.sheaf.xif.paper.Mzk1P0LQReadoutSignActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LNormalizationJointActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LNormalizationActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LReadoutLogActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LQReadoutSignActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LNormalizationSignActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LNormalizationExplicitActual
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
theorem lThetaNormFactor_gt_theta_of_theta_nonneg
    (h : 0 ≤ thetaReadActual I place) :
    thetaReadActual I place < lThetaNormFactor I place := by
  rw [lThetaNormFactor_eq_theta_sub_qRead]
  have hq : qReadActual I place < 0 := qReadActual_neg I place
  linarith
theorem lThetaNormFactor_pos_of_theta_nonneg
    (h : 0 ≤ thetaReadActual I place) :
    0 < lThetaNormFactor I place :=
  lt_of_le_of_lt h (lThetaNormFactor_gt_theta_of_theta_nonneg I place h)
end LeanFormal.IUT.XiFPaper.Mzk1P0LNormalizationJointActual