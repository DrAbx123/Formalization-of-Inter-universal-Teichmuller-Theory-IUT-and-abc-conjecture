import tmp.sheaf.xif.paper.Mzk1P1StepProviderF4bActual
import tmp.sheaf.xif.paper.Mzk1P1StepMaxDeg2Actual
import tmp.sheaf.xif.paper.Mzk1F0StepTransportProvedActual

/-! # Mzk1StepProviderPrimeAssembly3Actual — StepProvider' from PROVED f1/f2/f4a"/f4b; f5 named

Real Lean (no sorry/axiom): final paper-level assembly of the one-step transfer StepProvider'
(beta' = f0(beta)) from
* PROVED f1/f2 (Mzk1StepProviderPrimeActual),
* PROVED f4a via finite-part decomposition (Mzk1P1StepMaxDeg2Actual),
* PROVED f4b strict count (Mzk1P1StepProviderF4bActual),
with only the f5 target transport kept as a named input.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeAssembly3Actual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1F0StepGeometryActual
open LeanFormal.IUT.XiFPaper.Mzk1P1StepMaxDeg2Actual
open LeanFormal.IUT.XiFPaper.Mzk1P1StepProviderF4bActual
open LeanFormal.IUT.XiFPaper.Mzk1F0StepTransportProvedActual

universe u

/-- StepProvider' from the PROVED f1/f2/f4a/f4b and the named f5 transport. -/
theorem stepProvider_prime_of_f4_final (htr : F0StepTransportInput) : StepProvider' := by
  intro S beta hbeta hgt
  obtain ⟨alpha0, halpha0S, hdeg⟩ := exists_maxDegP_finite S hgt
  refine ⟨alpha0, stepSetP1 S alpha0, f0Map alpha0 beta, halpha0S, hdeg, rfl, ?_,
    htr S beta alpha0⟩
  have hle : maxDegP (stepSetP1 S alpha0) <= maxDegP S :=
    maxDegP_stepSetP1_le_alt S alpha0 halpha0S hdeg
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, numMaxP_stepSetP1_lt S alpha0 (by omega) halpha0S hdeg heq⟩

#check stepProvider_prime_of_f4_final

end LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeAssembly3Actual
end
