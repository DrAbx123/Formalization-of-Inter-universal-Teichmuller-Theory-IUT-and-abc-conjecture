import tmp.sheaf.xif.paper.Mzk1P1StepProviderF4bActual
import tmp.sheaf.xif.paper.Mzk1P1StepMaxDegActual
import tmp.sheaf.xif.paper.Mzk1StepProviderFromFixedBetaActual

/-! # Mzk1StepProviderPrimeAssembly2Actual — StepProvider' from PROVED f4a+f4b, f5 named

Real Lean (no sorry/axiom): the paper's one-step transfer StepProvider' assembled from
* PROVED f1/f2 (Mzk1StepProviderPrimeActual),
* PROVED f4a maxDegP non-increase (Mzk1P1StepMaxDegActual),
* PROVED f4b strict numMax count (Mzk1P1StepProviderF4bActual),
with only the f5 target transport remaining as a named input (no fake proof).
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeAssembly2Actual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1StepMaxDegActual
open LeanFormal.IUT.XiFPaper.Mzk1P1StepProviderF4bActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderFromFixedBetaActual

universe u

/-- StepProvider' from the PROVED f1/f2/f4a/f4b and the named f5 transport. -/
theorem stepProvider_prime_of_f4 (htr : F0StepTransportInput) : StepProvider' := by
  intro S beta hbeta hgt
  obtain ⟨alpha0, halpha0S, hdeg⟩ := exists_maxDegP_finite S hgt
  refine ⟨alpha0, stepSetP1 S alpha0, f0Map alpha0 beta, halpha0S, hdeg, rfl, ?_,
    htr S beta alpha0⟩
  have hle : maxDegP (stepSetP1 S alpha0) <= maxDegP S :=
    maxDegP_stepSetP1_le S alpha0 hdeg
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, numMaxP_stepSetP1_lt S alpha0 (by omega) halpha0S hdeg heq⟩

#check stepProvider_prime_of_f4

end LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeAssembly2Actual
end
