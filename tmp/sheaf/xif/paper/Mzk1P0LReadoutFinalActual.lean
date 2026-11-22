import tmp.sheaf.xif.paper.Mzk1P0LReadoutInstanceActual
/-! CONSUMER RE-EXPORT — re-exports an existing theorem; not a new proof. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LReadoutFinalActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0LReadoutInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
theorem qRead_final :
    qRead I place = -|Real.log ‖(C3LAt I place).q.q‖| := qRead_eq I place
theorem qRead_nonpos_final : qRead I place ≤ 0 := qRead_nonpos I place
end LeanFormal.IUT.XiFPaper.Mzk1P0LReadoutFinalActual