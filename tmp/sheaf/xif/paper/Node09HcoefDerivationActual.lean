import tmp.sheaf.xif.paper.Node09ResidualInputsActual
import tmp.sheaf.xif.paper.Mzk1PerPlaceInequalityActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ActualRamifiedDataActual
open LeanFormal.IUT.XiFPaper.Node09ResidualInputsActual
open LeanFormal.IUT.XiFPaper.Mzk1PerPlaceInequalityActual
namespace LeanFormal.IUT.XiFPaper.Node09HcoefDerivationActual
variable {l : PrimeGeFive} (X : N8NativeInput l)
variable {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]
/-- Attempt: derive per-place coefficient comparison from actual data. -/
theorem hcoef_actual (i : FinitePlaceAtPrime F p) (Fdeg l : ℝ) :
    CoeffComparison ((actualFn i : ℝ)) Fdeg l ((chosenA i : ℝ)) := by
  unfold CoeffComparison
end LeanFormal.IUT.XiFPaper.Node09HcoefDerivationActual
end
