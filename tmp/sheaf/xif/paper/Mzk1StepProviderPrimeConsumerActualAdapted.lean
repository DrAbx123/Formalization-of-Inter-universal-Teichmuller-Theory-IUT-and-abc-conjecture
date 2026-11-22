import tmp.sheaf.xif.paper.Mzk1P1MeasureDecreaseAssemblyActualAdapted

/-! # Mzk1StepProviderPrimeConsumerActualAdapted — StepProvider' from PROVED f1/f2/f4a + named f4b/f5

Real Lean (no sorry/axiom): final assembly of the paper's one-step transfer: f1 (point
selection) and f2 (step target) are PROVED; f4a (P1 maximal-degree non-increase) is PROVED
in Mzk1P1StepMaxDegActual; only f4b (numMax strict statement) and f5 (target transport)
remain named.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeConsumerActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderGapStatementsActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureDecreaseAssemblyActualAdapted

attribute [local instance] Classical.decEq

universe u

/-- StepProvider' from the PROVED f4a and the two remaining named inputs (f4b/f5). -/
theorem stepProvider'_of_f4a_and_named (hnum : P1NumMaxStrictStatement)
    (htr : F0StepTransportInput) : StepProvider' :=
  stepProvider'_of_named (p1MeasureDecrease_of_f4a_and_numMax hnum) htr

/-- Row record. -/
def stepProviderPrimeConsumerRows : List (String × String) :=
  [ ("stepProvider'_of_f4a_and_named", "PROVED CONDITIONAL (f1/f2/f4a PROVED; f4b/f5 named)") ]

theorem stepProviderPrimeConsumerRows_length : stepProviderPrimeConsumerRows.length = 1 := rfl

#check stepProvider'_of_f4a_and_named

end LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeConsumerActualAdapted
end
