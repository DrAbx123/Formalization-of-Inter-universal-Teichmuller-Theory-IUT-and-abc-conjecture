/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1SplitPredicateBridgeActual
import tmp.sheaf.xif.paper.Mzk1TateSquareCriterionActual
import TateCurvesTheta.Converse.QuadraticTwist
import Mathlib.Tactic

/-! # Mzk1SplitBridgeCompletionActual — (a)/(b) core and (ii) composition (A828, qpilot)

* (a) arithmetic core: `norm_j_eq` (`norm j = norm c4^3 / norm Delta`) and
  `one_lt_norm_j_of_norm`: `norm c4 = 1`, `norm Delta < 1` imply `1 < norm j`.
  Needed input from the Mathlib minimal-model class: the valuation/norm dictionary on
  `CompletionIntegers place` (`valuation c4 = 1 -> norm c4 = 1`, `valuation Delta < 1
  -> norm Delta < 1`).
* (b) algebraic core: `isSquare_gamma_of_isSquare_neg_mul`: `IsSquare (-c4*c6)` gives
  `IsSquare gamma(W)`. Needed input: lifting the residue splitting to
  `IsSquare (-c4*c6)` in K (Hensel-type root lifting via completeness).
* Composition: `leanformal_split_realization`: ellipticity + `1 < norm j` +
  `IsSquare gamma` give the base-level realization `exists t C, C • canonical(t.q) = W`.
  So (ii) is closed modulo exactly the two input lemmas; (iii) stays PENDING.

No axiom, no sorry, no `True` placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1SplitBridgeCompletionActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1SplitPredicateBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1TateSquareCriterionActual

/-! ### (a) -/

section NormJ

variable {K : Type*} [NormedField K]

theorem norm_j_eq (W : WeierstrassCurve K) [W.IsElliptic] :
    ‖W.j‖ = ‖W.c₄‖ ^ 3 / ‖W.Δ‖ := by
  rw [TateCurvesTheta.j_eq_div, norm_div, norm_pow]

theorem one_lt_norm_j_of_norm (W : WeierstrassCurve K) [W.IsElliptic]
    (h4 : ‖W.c₄‖ = 1) (hΔ : ‖W.Δ‖ < 1) (hΔ0 : W.Δ ≠ 0) :
    1 < ‖W.j‖ := by
  have hΔpos : 0 < ‖W.Δ‖ := norm_pos_iff.mpr hΔ0
  rw [norm_j_eq W, h4, one_pow]
  exact one_lt_one_div hΔpos hΔ

end NormJ

/-! ### (b) -/

section GammaSquare

variable {K : Type*} [Field K]

theorem isSquare_gamma_of_isSquare_neg_mul (W : WeierstrassCurve K)
    (hc6 : W.c₆ ≠ 0)
    (h : IsSquare (-W.c₄ * W.c₆)) :
    IsSquare (TateCurvesTheta.gammaInvariant W) := by
  obtain ⟨x, hx⟩ := h
  have hc6sq : W.c₆ ^ 2 ≠ 0 := pow_ne_zero 2 hc6
  have hγ : TateCurvesTheta.gammaInvariant W =
      (-W.c₄ * W.c₆) / (W.c₆ ^ 2) := by
    rw [TateCurvesTheta.gammaInvariant_def]
    field_simp
  rw [hγ, hx]
  refine ⟨x / W.c₆, ?_⟩
  field_simp

end GammaSquare

/-! ### Composition -/

variable {F : Type*} [Field F] [NumberField F]
variable (place : NumberField.FinitePlace F)
variable [IsUltrametricDist (Completion place)] [CompleteSpace (Completion place)]

theorem leanformal_split_realization
    (X : PuncturedEllipticCurve F)
    (hEll : (X.curve.baseChange (Completion place)).IsElliptic)
    (hj : 1 < ‖(X.curve.baseChange (Completion place)).j‖)
    (hγ : IsSquare (TateCurvesTheta.gammaInvariant
      (X.curve.baseChange (Completion place)))) :
    ∃ (t : TateCurvesTheta.TateParameter (Completion place))
      (C : WeierstrassCurve.VariableChange (Completion place)),
      C • TateCurve.weierstrassCurve (Completion place) (t.q : Completion place) =
        (X.curve.baseChange (Completion place)) := by
  have hvendor : TateCurvesTheta.HasSplitMultiplicativeReduction
      (X.curve.baseChange (Completion place)) :=
    vendor_split_of_leanformal place X hEll hj hγ
  haveI := hEll
  exact split_realization_canonical place (X.curve.baseChange (Completion place)) hvendor

/-! ### Rows -/

def completionRows : List (String × String) :=
  [ ("(a) norm j = norm c4^3 / norm Delta", "PROVED"),
    ("(a) norm c4 = 1, norm Delta < 1 => 1 < norm j", "PROVED"),
    ("(a) valuation => norm on CompletionIntegers", "MISSING (valuation/norm dictionary)"),
    ("(b) IsSquare(-c4*c6) => IsSquare gamma", "PROVED"),
    ("(b) residue split => IsSquare(-c4*c6) in K", "MISSING (Hensel-type lifting)"),
    ("(ii) realization from ellipticity + norm j > 1 + square gamma", "PROVED (composition)"),
    ("(ii) from LeanFormal HasSplitMultiplicativeReductionAt alone", "PENDING (via (a),(b))"),
    ("(iii) TatePointComparison point uniformization", "MISSING (analytic)") ]

theorem completionRows_length : completionRows.length = 8 := rfl

#check norm_j_eq
#check one_lt_norm_j_of_norm
#check isSquare_gamma_of_isSquare_neg_mul
#check leanformal_split_realization
#check completionRows_length

end LeanFormal.IUT.XiFPaper.Mzk1SplitBridgeCompletionActual
end
