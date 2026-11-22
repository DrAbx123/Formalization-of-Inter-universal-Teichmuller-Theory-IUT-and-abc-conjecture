import tmp.sheaf.xif.paper.Mzk1StepProviderPrimeAssembly2Actual
import tmp.sheaf.xif.paper.Mzk1P1MeasureDecreaseAssemblyActual
import tmp.sheaf.xif.paper.Mzk1StepProviderFromFixedBetaActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1F4bStepProviderClosureActual — A480 f4b -> StepProvider closure consumer

Real Lean umbrella assembling the existing f4b assets:

* `p1MeasureDecrease_from_f4b`: the f4b statement (`P1NumMaxStrictStatement`)
  yields the P1 lex measure decrease (`P1MeasureDecreaseInput`) through the
  already-proved f4a max-degree non-increase
  (`Mzk1P1MeasureDecreaseAssemblyActual.p1MeasureDecrease_of_f4a_and_numMax`);
* `stepProvider_of_f4b`: the paper one-step transfer `StepProvider'` from the
  PROVED f1/f2/f4a/f4b and the single named f5 target transport
  (`Mzk1StepProviderPrimeAssembly2Actual.stepProvider_prime_of_f4`);
* `stepProvider_of_f4b_named_f4`: the same transfer routed through the named
  f4b statement and the fixed-beta assembly;
* `f4b_stepProvider_package`: the measure-decrease and transfer conclusions
  jointly.

No sorry/axioms; no closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1F4bStepProviderClosureActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderGapStatementsActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderFromFixedBetaActual
open LeanFormal.IUT.XiFPaper.Mzk1P1StepMaxDegActual
open LeanFormal.IUT.XiFPaper.Mzk1P1StepProviderF4bActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeAssembly2Actual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureDecreaseAssemblyActual

universe u

/-- f4b statement -> P1 lex measure decrease (f4a already proved). -/
theorem p1MeasureDecrease_from_f4b (hnum : P1NumMaxStrictStatement) :
    P1MeasureDecreaseInput :=
  p1MeasureDecrease_of_f4a_and_numMax hnum

/-- StepProvider' from the proved f4a/f4b and the named f5 transport. -/
theorem stepProvider_of_f4b (htr : F0StepTransportInput) : StepProvider' :=
  stepProvider_prime_of_f4 htr

/-- StepProvider' via the named f4b statement and the fixed-beta assembly. -/
theorem stepProvider_of_f4b_named_f4 (hnum : P1NumMaxStrictStatement)
    (htr : F0StepTransportInput) : StepProvider' :=
  stepProvider_of_fixedBeta (p1MeasureDecrease_from_f4b hnum) htr

/-- Joint f4b -> StepProvider package. -/
theorem f4b_stepProvider_package (hnum : P1NumMaxStrictStatement)
    (htr : F0StepTransportInput) :
    P1MeasureDecreaseInput ∧ StepProvider' ∧ StepProvider' :=
  ⟨p1MeasureDecrease_from_f4b hnum,
   stepProvider_of_f4b htr,
   stepProvider_of_f4b_named_f4 hnum htr⟩

#check p1MeasureDecrease_from_f4b
#check stepProvider_of_f4b
#check f4b_stepProvider_package

end LeanFormal.IUT.XiFPaper.Mzk1F4bStepProviderClosureActual
end