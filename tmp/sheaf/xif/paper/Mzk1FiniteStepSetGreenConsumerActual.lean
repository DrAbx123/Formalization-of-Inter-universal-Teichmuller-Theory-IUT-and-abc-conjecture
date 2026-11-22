import tmp.sheaf.xif.paper.Mzk1NestedInductionActual

/-! # Mzk1FiniteStepSetGreenConsumerActual — consumer of the PROVED finite f4a

Real Lean (no sorry/axiom): consumer re-export of the existing PROVED finite step-set
degree lemmas from the green Mzk1NestedInductionActual.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetGreenConsumerActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual

attribute [local instance] Classical.decEq

universe u

/-- Consumer: maxDeg does not increase under the f0 step (existing PROVED lemma). -/
theorem maxDeg_stepSet_le_consumer (S : Finset Qbar) (alpha0 : Qbar)
    (halpha0 : alpha0 ∈ S) (hdeg : degQ alpha0 = maxDeg S) :
    maxDeg (stepSet S alpha0) <= maxDeg S :=
  maxDeg_stepSet_le S alpha0 halpha0 hdeg

/-- Consumer: the strictly smaller finite max-count on the stable branch (existing PROVED). -/
theorem numMax_stepSet_lt_consumer (S : Finset Qbar) (alpha0 : Qbar)
    (halpha0 : alpha0 ∈ S) (hdeg : degQ alpha0 = maxDeg S) (h2 : 2 <= degQ alpha0)
    (hsame : maxDeg (stepSet S alpha0) = maxDeg S) :
    numMax (stepSet S alpha0) < numMax S :=
  numMax_stepSet_lt S alpha0 halpha0 hdeg h2 hsame

def finiteStepSetGreenConsumerRows : List (String × String) :=
  [ ("maxDeg_stepSet_le_consumer", "PROVED (re-export)"),
    ("numMax_stepSet_lt_consumer", "PROVED (re-export)") ]

theorem finiteStepSetGreenConsumerRows_length : finiteStepSetGreenConsumerRows.length = 2 := rfl

#check maxDeg_stepSet_le_consumer

end LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetGreenConsumerActual
end
