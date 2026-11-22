import tmp.sheaf.xif.paper.Mzk1StepProviderPrimeActual
import tmp.sheaf.xif.paper.Mzk1F0StepGeometryActual
import tmp.sheaf.xif.paper.Mzk1NestedInductionActual
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import tmp.sheaf.xif.paper.PaperScopeLemma24Actual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1StepProviderFromFixedBetaActual — StepProvider' from fixed-beta choice + transport

Adapts the pending StepProviderPrimeAssembly file (fresh path): the paper one-step
transfer StepProvider' (beta' = f0(beta)) follows from two explicit named inputs:
(f4) P1 measure decrease for stepSetP1 and (f5) target transport along f0Map.
f1 (alpha0 selection) and f2 (S' construction) are reused from the EXIT0
Mzk1StepProviderPrimeActual.  No closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepProviderFromFixedBetaActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1F0StepGeometryActual
open LeanFormal.IUT.XiFPaper.PaperScopeLemma24Actual

/-- NAMED INPUT (f4): stepSetP1 has lexicographically smaller (maxDegP,numMaxP). -/
def P1MeasureDecreaseInput : Prop :=
  forall (S : Finset (P1Point Qbar)) (alpha0 : Qbar),
    1 < maxDegP S -> degQ alpha0 = maxDegP S ->
      Prod.Lex (· < ·) (· < ·)
        (maxDegP (stepSetP1 S alpha0), numMaxP (stepSetP1 S alpha0))
        (maxDegP S, numMaxP S)

/-- NAMED INPUT (f5): f0-step target transport back to (S,beta). -/
def F0StepTransportInput : Prop :=
  forall (S : Finset (P1Point Qbar)) (beta : P1Point Qbar) (alpha0 : Qbar),
    PaperScopeLemma24Target (stepSetP1 S alpha0) (f0Map alpha0 beta) ->
      PaperScopeLemma24Target S beta

/-- StepProvider' from f1+f2 (reused) and the two explicit named inputs. -/
theorem stepProvider_of_fixedBeta (hmu : P1MeasureDecreaseInput)
    (htr : F0StepTransportInput) : StepProvider' := by
  intro S beta hbeta hgt
  obtain ⟨alpha0, halpha0S, hdeg⟩ := exists_maxDegP_finite S hgt
  exact ⟨alpha0, stepSetP1 S alpha0, f0Map alpha0 beta, halpha0S, hdeg, rfl,
    hmu S alpha0 hgt hdeg, htr S beta alpha0⟩

/-- The same input-level assembly with beta' = f0Map alpha0 beta exposed. -/
theorem stepProvider_beta_eq (hmu : P1MeasureDecreaseInput)
    (htr : F0StepTransportInput) (S : Finset (P1Point Qbar)) (beta : P1Point Qbar)
    (hbeta : beta ∉ S) (hgt : 1 < maxDegP S) :
    ∃ (alpha0 : Qbar) (S' : Finset (P1Point Qbar)) (beta' : P1Point Qbar),
      P1Point.ofFinite alpha0 ∈ S ∧ degQ alpha0 = maxDegP S ∧
        beta' = f0Map alpha0 beta ∧
          Prod.Lex (· < ·) (· < ·) (maxDegP S', numMaxP S') (maxDegP S, numMaxP S) ∧
            (PaperScopeLemma24Target S' beta' -> PaperScopeLemma24Target S beta) :=
  stepProvider_of_fixedBeta hmu htr S beta hbeta hgt

def stepProviderFromFixedBetaRows : List (String × String × String) :=
  [ ("named inputs", "P1MeasureDecreaseInput / F0StepTransportInput", "NAMED"),
    ("StepProvider'", "stepProvider_of_fixedBeta", "PROVED (conditional on named inputs)"),
    ("beta' exposure", "stepProvider_beta_eq", "PROVED (conditional)"),
    ("scope", "f1/f2 reused; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem stepProviderFromFixedBetaRows_length : stepProviderFromFixedBetaRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1StepProviderFromFixedBetaActual

end
