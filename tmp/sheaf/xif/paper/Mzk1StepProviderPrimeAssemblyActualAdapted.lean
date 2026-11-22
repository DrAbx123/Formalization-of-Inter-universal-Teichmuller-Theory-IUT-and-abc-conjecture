import tmp.sheaf.xif.paper.Mzk1StepProviderPrimeActual
import tmp.sheaf.xif.paper.Mzk1F0StepGeometryActual

/-! # Mzk1StepProviderPrimeAssemblyActualAdapted — StepProvider' from two explicit named inputs

Real Lean (no sorry/axiom): the paper's one-step transfer StepProvider' (beta'=f0(beta),
A424) follows from exactly two named inputs:
  (i) P1 measure decrease for the concrete step target stepSetP1 (f4a/f4b combined);
  (ii) target transport along beta' = f0(beta) (f5; paper composition f' comp f0).
The alpha0 selection (f1) and S' construction (f2) are PROVED in
Mzk1StepProviderPrimeActual and consumed here.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeAssemblyActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1F0StepGeometryActual
open LeanFormal.IUT.XiFPaper.PaperScopeLemma24Actual

attribute [local instance] Classical.decEq

universe u

/-- NAMED INPUT (f4): the concrete P1 step target stepSetP1 has lexicographically smaller
(maxDegP,numMaxP) measure than S. -/
def P1MeasureDecreaseInput : Prop :=
  forall (S : Finset (P1Point Qbar)) (alpha0 : Qbar),
    1 < maxDegP S -> degQ alpha0 = maxDegP S ->
      Prod.Lex (· < ·) (· < ·)
        (maxDegP (stepSetP1 S alpha0), numMaxP (stepSetP1 S alpha0))
        (maxDegP S, numMaxP S)

/-- NAMED INPUT (f5): target transport from S' = stepSetP1 S alpha0 with
beta' = f0Map alpha0 beta back to (S, beta). -/
def F0StepTransportInput : Prop :=
  forall (S : Finset (P1Point Qbar)) (beta : P1Point Qbar) (alpha0 : Qbar),
    PaperScopeLemma24Target (stepSetP1 S alpha0) (f0Map alpha0 beta) ->
      PaperScopeLemma24Target S beta

/-- StepProvider' assembled from f1 (PROVED), f2 (PROVED) and the two named inputs. -/
theorem stepProvider'_of_named (hmu : P1MeasureDecreaseInput)
    (htr : F0StepTransportInput) : StepProvider' := by
  intro S beta hbeta hgt
  obtain ⟨alpha0, halpha0S, hdeg⟩ := exists_maxDegP_finite S hgt
  exact ⟨alpha0, stepSetP1 S alpha0, f0Map alpha0 beta, halpha0S, hdeg, rfl,
    hmu S alpha0 hgt hdeg, htr S beta alpha0⟩

/-- Rows. -/
def stepProviderPrimeAssemblyRows : List (String × String) :=
  [ ("P1MeasureDecreaseInput (f4)", "NAMED"),
    ("F0StepTransportInput (f5)", "NAMED"),
    ("stepProvider'_of_named", "PROVED CONDITIONAL (f1+f2 proved, f4+f5 named)") ]

theorem stepProviderPrimeAssemblyRows_length : stepProviderPrimeAssemblyRows.length = 3 := rfl

#check P1MeasureDecreaseInput
#check F0StepTransportInput
#check stepProvider'_of_named

end LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeAssemblyActualAdapted
end
