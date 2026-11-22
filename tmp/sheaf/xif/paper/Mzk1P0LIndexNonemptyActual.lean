import tmp.sheaf.xif.paper.Mzk1P0LPaperInstanceActual
import LeanFormal.IUT.IUTI.HodgeTheater.LocalPrimePlaces
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorIntegralRegion
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LIndexNonemptyActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open MeasureTheory
universe ua upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
theorem finitePrimePlace_two_seven_nonempty : Nonempty (FinitePrimePlace 2 7) :=
  ⟨⟨2, by norm_num [LeanFormal.IUT.primeStrip]⟩⟩
theorem tensorIndex_nonempty : Nonempty (C3LAt I place).tensorIndex := by
  change Nonempty (FinitePrimePlace 2 7)
  exact finitePrimePlace_two_seven_nonempty
end LeanFormal.IUT.XiFPaper.Mzk1P0LIndexNonemptyActual