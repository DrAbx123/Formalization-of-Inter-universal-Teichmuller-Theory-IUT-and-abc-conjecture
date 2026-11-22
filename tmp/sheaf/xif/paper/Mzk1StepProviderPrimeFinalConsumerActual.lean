import tmp.sheaf.xif.paper.Mzk1StepProviderPrimeConsumerActual

/-! # Mzk1StepProviderPrimeFinalConsumerActual — final consumer record of StepProvider'

Real Lean (no sorry/axiom): consumer record conjoining the StepProvider' assembly with the
explicit paper-scope reading of its fields (f1/f2/f4a proved; f4b/f5 named).  Registry 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeFinalConsumerActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderGapStatementsActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeConsumerActual

attribute [local instance] Classical.decEq

universe u

/-- Consumer: StepProvider' holds given the two named inputs. -/
theorem stepProviderPrime_consumer (hnum : P1NumMaxStrictStatement)
    (htr : F0StepTransportInput) : StepProvider' :=
  stepProvider'_of_f4a_and_named hnum htr

/-- The paper-scope target follows from the step provider and the base case (PROVED
elsewhere): consumer form of the nested induction step, conditional on f4b/f5. -/
theorem paperScope_nestedStep_consumer (hnum : P1NumMaxStrictStatement)
    (htr : F0StepTransportInput) (S : Finset (P1Point Qbar)) (beta : P1Point Qbar)
    (hbeta : beta ∉ S) (hgt : 1 < maxDegP S) :
    exists (alpha0 : Qbar) (S' : Finset (P1Point Qbar)) (beta' : P1Point Qbar),
      P1Point.ofFinite alpha0 ∈ S ∧ degQ alpha0 = maxDegP S ∧
        beta' = f0Map alpha0 beta ∧
          Prod.Lex (· < ·) (· < ·) (maxDegP S', numMaxP S') (maxDegP S, numMaxP S) := by
  have hsp := stepProviderPrime_consumer hnum htr
  obtain ⟨alpha0, S', beta', hmem, hdeg, hbeta', hlex, _htrans⟩ :=
    hsp S beta hbeta hgt
  exact ⟨alpha0, S', beta', hmem, hdeg, hbeta', hlex⟩

def stepProviderPrimeFinalRows : List (String × String) :=
  [ ("stepProviderPrime_consumer", "PROVED CONDITIONAL (f4b/f5 named)"),
    ("paperScope_nestedStep_consumer", "PROVED CONDITIONAL (f4b/f5 named)") ]

theorem stepProviderPrimeFinalRows_length : stepProviderPrimeFinalRows.length = 2 := rfl

#check paperScope_nestedStep_consumer

end LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeFinalConsumerActual
end
