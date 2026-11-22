/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A618ProofQpilotActual
import tmp.sheaf.xif.paper.Mzk1HeightWeightFromTripleQpilotActual
import tmp.sheaf.xif.paper.Mzk1GapShapeAuditQpilotActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesModelQpilotActual

/-! # Mzk1A618MachineProofReexportQpilotActual — A618 machine-proof thin re-export

A645 (qpilot lane): thin re-export of the green A618 machine proofs (height/
volume estimates, model reduction) plus the triple-comparison height-weight bound.
(`Mzk1A618MachineProofActual` is another lane's file; this is the qpilot prefix
re-export only, no overwrite.) -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1A618MachineProofReexportQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesModelQpilotActual
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1A618ProofQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1HeightWeightFromTripleQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1GapShapeAuditQpilotActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual
open MeasureTheory
open scoped ENNReal

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [Nonempty (Bad (nativePlaceSelection T))]

/-- A618 re-export: height estimate (thin). -/
theorem a618Reexport_heightEstimate {X : Type u} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon)
    (h0 : 0 ≤ epsilon) (h1 : epsilon ≤ 1) :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + 3 * epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (1 + epsilon) * ((W.logVolume W.hull).toReal + D) :=
  a618_heightEstimate C h0 h1

/-- A618 re-export: volume estimate (thin). -/
theorem a618Reexport_volumeEstimate {X : Type u} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon) :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume (C.comparisonRegion a b c)).toReal ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.hull).toReal + D :=
  a618_volumeEstimate C

/-- A618 re-export: model reduction (thin). -/
theorem a618Reexport_modelReduction {X : Type u} {W : IQHullLogVolumeInterface X}
    (C : ∀ epsilon : Real, 0 < epsilon → Cor312EpsilonArithmeticComparison W epsilon) :
    HeightWeightBoundShape :=
  a618_modelReduction C

/-- A618 re-export: height-weight bound from a single triple comparison. -/
theorem a618Reexport_tripleBound
    (point : Nat → Nat → Nat → S1902Carrier T)
    (C : TripleDependentComparison T point) :
    HeightWeightBoundShape :=
  heightWeightBoundShape_of_tripleComparison T point C

#check a618Reexport_heightEstimate
#check a618Reexport_tripleBound

end LeanFormal.IUT.XiFPaper.Mzk1A618MachineProofReexportQpilotActual
end
