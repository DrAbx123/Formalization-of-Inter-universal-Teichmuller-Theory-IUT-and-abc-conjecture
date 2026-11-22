import tmp.sheaf.xif.paper.Mzk1StepProviderPrimeActual

/-! # Mzk1StepProviderGapStatementsActual — explicit statement layer for the C-gap nodes

Real Lean statements (no sorry/axiom) for the two remaining Problem C step-provider gaps,
phrased against the existing concrete objects in Mzk1StepProviderPrimeActual:
  (i) P1 numMax strict decrease when maxDegP is stable (f4b);
  (ii) fixed-beta choice statement (alpha0/Galois; the paper uses beta'=f0(beta)).
The statements are definitions; the iff lemmas are definitional.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1StepProviderGapStatementsActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

attribute [local instance] Classical.decEq

universe u

/-- (f4b) P1 numMax strict decrease on the stable-maxDegP branch of the f0 step. -/
def P1NumMaxStrictStatement : Prop :=
  forall (S : Finset (P1Point Qbar)) (alpha0 : Qbar),
    1 < maxDegP S -> degQ alpha0 = maxDegP S ->
      maxDegP (stepSetP1 S alpha0) = maxDegP S ->
        numMaxP (stepSetP1 S alpha0) < numMaxP S

/-- (f5/fixed-beta) fixed-beta choice statement: alpha0 selection with beta not in the
image target set and measure decrease. -/
def FixedBetaChoiceStatement : Prop := StepProviderFixedBetaChoiceInput

/-- The statement is definitionally the existing named interface. -/
theorem fixedBetaChoice_iff : FixedBetaChoiceStatement ↔ StepProviderFixedBetaChoiceInput :=
  Iff.rfl

/-- Rows. -/
def gapStatementsRows : List (String × String) :=
  [ ("P1NumMaxStrictStatement (f4b)", "DEFINED; iff existing named interface"),
    ("FixedBetaChoiceStatement (f5)", "DEFINED; iff existing named interface") ]

theorem gapStatementsRows_length : gapStatementsRows.length = 2 := rfl

#check P1NumMaxStrictStatement
#check FixedBetaChoiceStatement

end LeanFormal.IUT.XiFPaper.Mzk1StepProviderGapStatementsActual
end
