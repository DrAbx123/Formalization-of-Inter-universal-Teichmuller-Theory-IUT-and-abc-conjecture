import tmp.sheaf.xif.paper.Node09HqMultConsumerActual
import tmp.sheaf.xif.paper.Mzk1ActualRamifiedDataActual
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1QVWeightedActual
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Node09HqMultConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1ActualRamifiedDataActual
variable {l : PrimeGeFive} (X : N8NativeInput l)
variable {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]
/-- Fiber/index interface: a total map from F-places at p to bad native places.
This is weaker than a bijection (which is generally false since Bad is a subset). -/
structure QVBadPlaceFiber where
  b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S)
/-- Fiber-weighted q sum `M_q = sum_i mult_i * log p_i`, no bijection claim. -/
noncomputable def MqFiber (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S)) : Real :=
  ∑ i : FinitePlaceAtPrime F p,
    fiberMult X b i * Real.log (residueNormBase ((b i).1))
/-- The fiber-weighted q sum is exactly the sum of the corresponding local
q_v log magnitudes (Node09 identity). -/
theorem MqFiber_eq_sum_localLog
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S)) :
    MqFiber (p := p) X b =
      ∑ i : FinitePlaceAtPrime F p, localLogMagnitude (qVFamily X.S (b i)) := by
  unfold MqFiber
  apply Finset.sum_congr rfl
  intro i _
  exact fiberMult_log_eq_localLogMagnitude X b i
/-- Node09 R1 consumer: per-place fiberMult bound feeds the actual A-term. -/
theorem actual_A_le_Lbar_add_Dbar_of_fiberMult
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (Fdeg l : Real) (logMu : FinitePlaceAtPrime F p → Real)
    (hlogp : ∀ i : FinitePlaceAtPrime F p,
      Real.log (((completionRationalPrime (i.val)).val : Nat) : Real) =
        Real.log (residueNormBase ((b i).1)))
    (h : ∀ i : FinitePlaceAtPrime F p,
      fiberMult X b i / (Fdeg * (2 * l)) *
          Real.log (residueNormBase ((b i).1)) ≤
        LeanFormal.IUT.XiFPaper.Mzk1ActualRamifiedDataActual.actualLogIdx i +
          (logMu i - (1 / (2 * l)) *
            LeanFormal.IUT.XiFPaper.Mzk1ActualRamifiedDataActual.actualLogIdx i)) :
    (1 / (2 * l)) * (∑ i : FinitePlaceAtPrime F p,
        fiberMult X b i / Fdeg *
          Real.log (((completionRationalPrime (i.val)).val : Nat) : Real)) ≤
      ∑ i : FinitePlaceAtPrime F p,
        (LeanFormal.IUT.XiFPaper.Mzk1ActualRamifiedDataActual.actualLogIdx i +
          (logMu i - (1 / (2 * l)) *
            LeanFormal.IUT.XiFPaper.Mzk1ActualRamifiedDataActual.actualLogIdx i)) :=
  Node09HqMultConsumerActual.actual_A_le_Lbar_add_Dbar_of_fiberMult X b Fdeg l logMu hlogp h
#check QVBadPlaceFiber
#check MqFiber
#check MqFiber_eq_sum_localLog
#check actual_A_le_Lbar_add_Dbar_of_fiberMult
end LeanFormal.IUT.XiFPaper.Mzk1QVWeightedActual
end