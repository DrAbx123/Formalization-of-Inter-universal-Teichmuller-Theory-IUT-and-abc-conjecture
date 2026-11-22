import tmp.sheaf.xif.paper.Mzk1P7ContractMarginConsumerActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P7GapContractConsumerActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.XiFPaper.Mzk1P7ContractMarginConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1P7GapRegisterActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- P7 7-gap contract consumer: the actual margin-1 witness feeds the
conditional Cor 3.12 contract assembly. -/
theorem p7_gap_contract_consumer
    (hmargin : qPilotLogVolumeReading P + 1 ≤ thetaPilotHullLogVolumeReal C3) :
    Cor312Conclusion
      (contractOfS3137Comparison C3 P (comparison_of_margin_one C3 P hmargin)) :=
  p7_conditional_contract_of_margin_one T C3 P hmargin

/-- The 7-gap margin row record has exactly seven entries. -/
theorem p7_margin7_rows_length : margin7Rows.length = 7 :=
  margin7Rows_length

#print axioms p7_gap_contract_consumer
#print axioms p7_margin7_rows_length
end LeanFormal.IUT.XiFPaper.Mzk1P7GapContractConsumerActual