/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C3BaseQIdentificationActual
import tmp.sheaf.xif.paper.Mzk1BaseChangeQCorrespondenceActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import Mathlib.Tactic
/-! # P4 C3 direct aggregation (conditional constructor, no S2135) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P4C3AggregationActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.XiFPaper.Mzk1C3BaseQIdentificationActual
open LeanFormal.IUT.XiFPaper.Mzk1BaseChangeQCorrespondenceActual
variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (P : PaperQPilotObjectActual (l := l) (I := I))
/-- Direct aggregate => C3 signed aggregation, no S2135. -/
theorem c3Aggregation_of_globalSum
    (agg : GlobalSumAggregation T I P) :
    QPilotC3SignedAggregation T I P :=
  qPilotC3SignedAggregation_of_aggregation T I P agg
#check c3Aggregation_of_globalSum
end LeanFormal.IUT.XiFPaper.Mzk1P4C3AggregationActual
end