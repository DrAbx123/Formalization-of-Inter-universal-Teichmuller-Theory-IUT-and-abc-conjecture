import tmp.sheaf.xif.paper.Mzk1P0LPaperInstanceActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LReadoutLogActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
theorem qReadActual_eq_logNorm :
    qReadActual I place = Real.log ‖(C3LAt I place).q.q‖ := by
  rw [qReadActual_eq]
  have hneg : Real.log ‖(C3LAt I place).q.q‖ < 0 :=
    Real.log_neg (qNorm_pos (C3LAt I place).q) (qNorm_lt_one (C3LAt I place).q)
  rw [abs_of_neg hneg]
  ring
theorem qReadActual_eq_localSignedLog :
    qReadActual I place = localSignedLog (C3LAt I place).q := by
  rw [qReadActual_eq_logNorm]
  rfl
#print axioms qReadActual_eq_logNorm
#print axioms qReadActual_eq_localSignedLog
end LeanFormal.IUT.XiFPaper.Mzk1P0LReadoutLogActual