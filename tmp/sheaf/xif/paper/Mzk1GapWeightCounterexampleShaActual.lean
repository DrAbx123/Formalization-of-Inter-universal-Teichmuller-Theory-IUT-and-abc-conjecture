import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# shehdd weight-model counterexample (Sha)

For the ABC triple `3 + 125 = 128` the rational point is `3/128`; given the
arithmetic-weight identity `arithmeticWeight (3/128) = Real.log 30` (supplied as an
explicit hypothesis, since the prime-support evaluation is heavy for `decide`), the
height `Real.log 128` is strictly larger.  Hence the pointwise
`height <= arithmeticWeight` substitution is FALSE; the real HeightEstimate must use
the paper region log-volume.  No gap is claimed.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1GapWeightCounterexampleShaActual

open LeanFormal.IUT

/-- `3 + 125 = 128` is an ABC (primitive additive) triple. -/
theorem triple_3_125_128 : IsABCTriple 3 125 128 := by
  unfold IsABCTriple PrimitiveAdditiveTriple
  decide

/-- Height of the point `3/128`: `Real.log 128`. -/
theorem height_3_128 :
    Height.logHeight₁ (abcRationalPoint 3 128) = Real.log 128 :=
  abcRationalPoint_logHeight₁ triple_3_125_128

/-- Conditional weight-model counterexample: if the arithmetic weight of `3/128` is
`Real.log 30`, then the weight is strictly smaller than the height. -/
theorem weight_model_counterexample_conditional
    (hweight : arithmeticWeight (abcRationalPoint 3 128) = Real.log 30) :
    arithmeticWeight (abcRationalPoint 3 128) <
      Height.logHeight₁ (abcRationalPoint 3 128) := by
  rw [hweight, height_3_128]
  exact Real.log_lt_log (by norm_num) (by norm_num)

/-- Conditional false pointwise statement. -/
theorem weight_model_pointwise_false_conditional
    (hweight : arithmeticWeight (abcRationalPoint 3 128) = Real.log 30) :
    ¬ (Height.logHeight₁ (abcRationalPoint 3 128) ≤
        arithmeticWeight (abcRationalPoint 3 128)) :=
  not_le.mpr (weight_model_counterexample_conditional hweight)

end LeanFormal.IUT.XiFPaper.Mzk1GapWeightCounterexampleShaActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1GapWeightCounterexampleShaActual.weight_model_counterexample_conditional
