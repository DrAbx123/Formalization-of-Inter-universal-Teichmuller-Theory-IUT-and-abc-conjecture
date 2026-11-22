import tmp.sheaf.xif.paper.Mzk1StepProviderPrimeAssembly3Actual
import tmp.sheaf.xif.paper.Mzk1F0StepTransportProvedActual

/-! # Mzk1StepProviderPrimeUnconditionalActual — StepProvider' with f5 discharged (real)

Real Lean (no sorry/axiom): the paper's one-step transfer StepProvider' (A424, beta'=f0(beta))
with all four ingredients PROVED:
* f1/f2 max-degree point selection + step target (Mzk1StepProviderPrimeActual),
* f4a max-degree non-increase (Mzk1P1StepMaxDeg2Actual),
* f4b strict P1 numMax count (Mzk1P1StepProviderF4bActual),
* f5 target transport (Mzk1F0StepTransportProvedActual, consuming the PROVED CV law).
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeUnconditionalActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeAssembly3Actual
open LeanFormal.IUT.XiFPaper.Mzk1F0StepTransportProvedActual

universe u

/-- **StepProvider' PROVED** (all four ingredients proved; no named inputs). -/
theorem stepProvider'_proved : StepProvider' :=
  stepProvider_prime_of_f4_final f0StepTransportInput_proved

#check stepProvider'_proved

end LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeUnconditionalActual
end
