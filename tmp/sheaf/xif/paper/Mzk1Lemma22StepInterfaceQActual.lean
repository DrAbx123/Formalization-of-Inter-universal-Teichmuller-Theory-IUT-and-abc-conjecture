import tmp.sheaf.xif.paper.Mzk1GChoiceDataOfHypothesesActual
import tmp.sheaf.xif.paper.Mzk1Lemma22HypPreservationActual
import tmp.sheaf.xif.paper.Mzk1GChoiceScaleActual
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# STEP 0 prior-art: step interface -> hits Mzk1GChoiceDataOfHypothesesActual (gChoiceData_of_hypotheses/stepExists_of_hypotheses), Mzk1Lemma22HypPreservationActual, Mzk1GChoiceScaleActual -> REUSE (interface only; existence proof TODO/named).

# Mzk1Lemma22StepInterfaceQActual — explicit Lemma 2.2 step interface over Q

MINIMAL GREEN VERSION per Lead: the explicit induction-step structure is DEFINED;
its existence theorem is recorded as a named statement (TODO), not proved here.
No fake; registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma22StepInterfaceQActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual

/-- Explicit one-step Lemma 2.2 data over Q^1. -/
structure Mzk1Lemma22StepInterfaceQ where
  source : Finset (P1Point ℚ)
  beta : P1Point ℚ
  g : ℚ[X]
  gdeg : 1 ≤ g.natDegree
  targetS : Finset (P1Point ℚ)
  beta' : P1Point ℚ
  targetS_eq : targetS = source.image (polyMapPoints g)
  beta'_eq : beta' = polyMapPoints g beta
  card_lt : targetS.card < source.card
  hImage : Lemma22Hypotheses targetS beta'
  preserves : ∀ p ∈ source, polyMapPoints g p ∈ targetS
  unramified : ∀ x : ℚ, polyMapPoints g (P1Point.ofFinite x) ∉ (↑targetS : Set (P1Point ℚ)) →
    g.derivative.eval x ≠ 0

/-- **EXISTENCE STATEMENT (named TODO; not proved in this minimal version).** -/
def step_interface_of_hypotheses_statement : Prop :=
  ∀ (S : Finset (P1Point ℚ)) (β : P1Point ℚ),
    Lemma22Hypotheses S β → 3 < S.card →
      ∃ st : Mzk1Lemma22StepInterfaceQ,
        st.source = S ∧ st.beta = β ∧ st.targetS.card < S.card

/-- Step-interface row record. -/
def stepInterfaceQRows : List (String × String × String) :=
  [ ("explicit step interface structure", "A", "DEFINED Mzk1Lemma22StepInterfaceQ")
  , ("step existence from Lemma22Hypotheses", "TODO", "NAMED: step_interface_of_hypotheses_statement") ]

theorem stepInterfaceQRows_length : stepInterfaceQRows.length = 2 := rfl

#check Mzk1Lemma22StepInterfaceQ
#check step_interface_of_hypotheses_statement
#check stepInterfaceQRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Lemma22StepInterfaceQActual
end