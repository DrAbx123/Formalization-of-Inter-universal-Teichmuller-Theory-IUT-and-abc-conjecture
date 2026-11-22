/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1GapComponentsQpilotActual
import tmp.sheaf.xif.paper.Mzk1HeightWeightFromTripleQpilotActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesModelQpilotActual

/-! # Mzk1GapChainConsumerQpilotActual — gap chain consumer wrap-up (A645)

Consumer of the gap components: absorbed bound for a fixed bridge datum and the
global height-weight bound for a mainline triple comparison. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GapChainConsumerQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesModelQpilotActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1GapComponentsQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1HeightWeightFromTripleQpilotActual
open MeasureTheory
open scoped ENNReal

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [Nonempty (Bad (nativePlaceSelection T))]

/-- Consumer: absorbed bound from a fixed bridge comparison datum. -/
theorem gapChain_absorbed {X : Type u} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon)
    (h0 : 0 ≤ epsilon) (h1 : epsilon ≤ 1) :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + 3 * epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (1 + epsilon) * ((W.logVolume W.hull).toReal + D) :=
  (gapComponentsOfComparison C).absorbed h0 h1

/-- Consumer: global height-weight bound from a mainline triple comparison. -/
theorem gapChain_tripleBound
    (point : Nat → Nat → Nat → S1902Carrier T)
    (C : TripleDependentComparison T point) :
    HeightWeightBoundShape :=
  heightWeightBoundShape_of_tripleComparison T point C

/-- The gap chain consumer bundle. -/
structure GapChainConsumer where
  absorbed : ∀ {X : Type u} {W : IQHullLogVolumeInterface X} {epsilon : Real}
    (C : Cor312EpsilonArithmeticComparison W epsilon),
    0 ≤ epsilon → epsilon ≤ 1 →
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + 3 * epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (1 + epsilon) * ((W.logVolume W.hull).toReal + D)
  tripleBound : ∀ (point : Nat → Nat → Nat → S1902Carrier T)
    (C : TripleDependentComparison T point), HeightWeightBoundShape

/-- The constructed gap chain consumer. -/
noncomputable def gapChainConsumer : GapChainConsumer T where
  absorbed := fun {X} {W} {epsilon} C h0 h1 => gapChain_absorbed C h0 h1
  tripleBound := fun point C => gapChain_tripleBound T point C

#check gapChainConsumer

end LeanFormal.IUT.XiFPaper.Mzk1GapChainConsumerQpilotActual
end
