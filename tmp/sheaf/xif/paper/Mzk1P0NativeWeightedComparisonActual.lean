/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P3NativeMassReductionActual
import tmp.sheaf.xif.paper.Mzk1P3MassIdentificationActual
import tmp.sheaf.xif.paper.Mzk1P2DetWeightedNonnegActual
import Mathlib.Tactic
/-! # P0.6 #1: weighted native comparison from blockwise R1.3 identification -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeWeightedComparisonActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P3NativeMassReductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P3MassIdentificationActual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetWeightedNonnegActual
open scoped BigOperators
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Blockwise R1.3 identification gives the weighted native comparison. -/
theorem nativeWeightedLogMassQ_le_L_of_blockwise
    (h : ∀ b : Bad (nativePlaceSelection T),
      R37R13NativeMassIdentification T b) :
    nativeWeightedLogMassQ T ≤ nativeWeightedLogMassL T := by
  have hdiff := nativeWeightedMassDifference_eq_p2R13_of_blockwise T h
  have hnonneg : 0 ≤ p2R13Exact T := p2R13Exact_nonneg T
  linarith
theorem nativeWeightedLogMassQ_le_L_iff :
    nativeWeightedLogMassQ T ≤ nativeWeightedLogMassL T ↔
      0 ≤ nativeWeightedLogMassL T - nativeWeightedLogMassQ T := by
  constructor <;> intro h <;> linarith
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeWeightedComparisonActual
end
