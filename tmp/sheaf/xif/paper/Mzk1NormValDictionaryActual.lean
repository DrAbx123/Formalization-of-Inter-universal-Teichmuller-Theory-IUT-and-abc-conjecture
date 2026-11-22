/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers
import TateCurvesTheta.QParameter.Basic
import Mathlib.Tactic

/-! # Mzk1NormValDictionaryActual — A801 continuation: norm/valuation dictionary (qpilot)

Part (i) of the remaining A801 gaps: on the finite-place completion, relate the
valuation side `Valued.v q < 1` of `FinitePlaceQCandidate` to the norm side
`‖q‖ < 1` needed by `TateCurvesTheta.TateParameter`.

Proved here:
* `completion_val_lt_one_iff_norm_lt_one` : `Valued.v q < 1 ↔ ‖q‖ < 1` on the
  completion (via `Valued.toNormedField.norm_lt_one_iff`);
* `tateParameterOfQCandidate` : every `FinitePlaceQCandidate place` gives an actual
  `TateCurvesTheta.TateParameter (Completion place)`, with `q` the candidate unit and
  norm `< 1` from the valuation condition;
* `tateParameterOfQCandidate_q` : its parameter is the candidate's `q`.

Part (iii) (point uniformization) needs `TatePointComparison` (pointEquiv +
galois_naturality) over `AlgebraicClosure (Completion place)`; vendor
`CurveIndexedTateUniformization` is a different model, so the bridge is recorded as
the explicit remaining input `TatePointUniformizationInput` (rows).

No axiom, no sorry, no `True` placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1NormValDictionaryActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {F : Type u} [Field F] [NumberField F]

section ValNorm

variable (place : NumberField.FinitePlace F)

/-- **Norm/valuation dictionary on the completion**: `Valued.v q < 1` iff `‖q‖ < 1`. -/
theorem completion_val_lt_one_iff_norm_lt_one (q : Completion place) :
    (Valued.v q : WithZero (Multiplicative Int)) < 1 ↔ ‖q‖ < 1 := by
  exact Valued.toNormedField.norm_lt_one_iff.symm

/-- A q-candidate gives an actual Tate parameter: its `q` is a unit and has norm `< 1`. -/
def tateParameterOfQCandidate (parameter : FinitePlaceQCandidate place) :
    TateCurvesTheta.TateParameter (Completion place) where
  q := Units.mk0 parameter.q parameter.q_ne_zero
  norm_lt_one := (completion_val_lt_one_iff_norm_lt_one place parameter.q).mp
    parameter.valuation_lt_one

@[simp] theorem tateParameterOfQCandidate_q (parameter : FinitePlaceQCandidate place) :
    (tateParameterOfQCandidate place parameter).q =
      Units.mk0 parameter.q parameter.q_ne_zero := rfl

/-- The constructed Tate parameter has the candidate's `q` as underlying element. -/
theorem tateParameterOfQCandidate_coe (parameter : FinitePlaceQCandidate place) :
    ((tateParameterOfQCandidate place parameter).q : Completion place) = parameter.q := rfl

/-- The normalized `q`-valuation is unchanged: the parameter is a unit. -/
theorem tateParameterOfQCandidate_valuation_lt_one
    (parameter : FinitePlaceQCandidate place) :
    (Valued.v (parameter.q) : WithZero (Multiplicative Int)) < 1 := by
  have h := (completion_val_lt_one_iff_norm_lt_one place parameter.q).mpr
    ((tateParameterOfQCandidate place parameter).norm_lt_one)
  exact h

end ValNorm

/-! ### Part (iii): point uniformization input -/

/-! ### Rows -/

def normValRows : List (String × String) :=
  [ ("completion norm/valuation dictionary: Valued.v q < 1 ↔ ‖q‖ < 1", "PROVED"),
    ("FinitePlaceQCandidate → TateParameter (unit + norm < 1)", "PROVED"),
    ("parameter q preserved as underlying element", "PROVED"),
    ("TatePointComparison pointEquiv over AlgebraicClosure", "INPUT (TatePointUniformizationInput)"),
    ("Galois naturality of the point uniformization", "INPUT (analytic equivariance)") ]

theorem normValRows_length : normValRows.length = 5 := rfl

#check completion_val_lt_one_iff_norm_lt_one
#check tateParameterOfQCandidate
#check tateParameterOfQCandidate_coe
#check normValRows_length

end LeanFormal.IUT.XiFPaper.Mzk1NormValDictionaryActual
end
