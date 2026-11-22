import tmp.sheaf.xif.paper.Mzk1P0LReadoutLogActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LQReadoutSignActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LReadoutLogActual
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
theorem qReadActual_neg : qReadActual I place < 0 := by
  rw [qReadActual_eq_logNorm]
  exact Real.log_neg (qNorm_pos (C3LAt I place).q) (qNorm_lt_one (C3LAt I place).q)
theorem qReadActual_eq_neg_localLogMagnitude :
    qReadActual I place = -localLogMagnitude (C3LAt I place).q := by
  rw [qReadActual_eq_localSignedLog]
  unfold localLogMagnitude
  ring
#print axioms qReadActual_neg
#print axioms qReadActual_eq_neg_localLogMagnitude
end LeanFormal.IUT.XiFPaper.Mzk1P0LQReadoutSignActual