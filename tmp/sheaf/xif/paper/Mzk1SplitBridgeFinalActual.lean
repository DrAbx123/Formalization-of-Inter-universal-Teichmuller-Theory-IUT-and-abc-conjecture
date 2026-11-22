/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1NormValDictionaryActual
import tmp.sheaf.xif.paper.Mzk1SplitBridgeCompletionActual
import LeanFormal.IUT.Foundations.NumberField.SourceTateParameterBridge
import TateCurvesTheta.Converse.WeierstrassIso
import Mathlib.Tactic

/-! # Mzk1SplitBridgeFinalActual — (a) closed; (ii) modulo IsSquare γ only (A833 update)

**(a) CLOSED (green LeanFormal re-export)**:
* `class_valuation_equiv_valued`: `Valued.v` is equivalent to the maximal-ideal
  valuation of `CompletionIntegers place` (LeanFormal
  `valued_isEquiv_maximalIdealValuation`), giving the translation of the Mathlib class
  conditions `valuation c4 = 1` / `valuation Δ < 1` to `Valued.v c4 = 1` /
  `Valued.v Δ < 1`;
* `norm_eq_one_of_valued_eq_one` (proved here): `Valued.v x = 1 → ‖x‖ = 1`;
* `norm_lt_one_of_valued_lt_one` (green dictionary);
* `norm_j_gt_one_of_split`: from `X.HasSplitMultiplicativeReductionAt place`,
  `1 < ‖(X.curve.baseChange (Completion place)).j‖` (LeanFormal
  `norm_j_gt_one_of_splitMultiplicativeReductionAt`).

**(ii) modulo exactly one input**: `split_realization_of_leanformal` gives the
base-level realization `∃ t C, C • canonical(t.q) = X.curve.baseChange (Completion place)`
from the LeanFormal split predicate, ellipticity, and `IsSquare (γ (X.curve.baseChange))`.
The only remaining input is (b′): residue-splitting ⇒ `IsSquare γ` in K (Hensel-type
lifting).  (iii) point uniformization stays PENDING.

No axiom, no sorry, no `True` placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1SplitBridgeFinalActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1NormValDictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1SplitBridgeCompletionActual

variable {F : Type*} [Field F] [NumberField F]
variable (place : NumberField.FinitePlace F)

/-! ### (a) class valuation ↔ `Valued.v` (green re-export) -/

theorem class_valuation_equiv_valued :
    (Valued.v : Valuation (Completion place) (WithZero (Multiplicative Int))).IsEquiv
      ((IsDiscreteValuationRing.maximalIdeal (CompletionIntegers place)).valuation
        (Completion place)) :=
  LeanFormal.IUT.SourceTateParameter.valued_isEquiv_maximalIdealValuation place

theorem norm_eq_one_of_valued_eq_one (x : Completion place)
    (h : (Valued.v x : WithZero (Multiplicative Int)) = 1) :
    ‖x‖ = 1 := by
  have hx0 : x ≠ 0 := by
    intro hx
    rw [hx] at h
    simp at h
  have hnot_lt : ¬ ‖x‖ < 1 :=
    fun hlt => absurd h ((completion_val_lt_one_iff_norm_lt_one place x).mpr hlt).ne
  have hle : 1 ≤ ‖x‖ := le_of_not_gt hnot_lt
  have hinv : Valued.v x⁻¹ = (1 : WithZero (Multiplicative Int)) := by
    rw [map_inv₀, h, inv_one]
  have hnot_lt_inv : ¬ ‖x⁻¹‖ < 1 :=
    fun hlt => absurd hinv
      ((completion_val_lt_one_iff_norm_lt_one place x⁻¹).mpr hlt).ne
  have hle_inv : 1 ≤ ‖x⁻¹‖ := le_of_not_gt hnot_lt_inv
  have hxnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hinvnorm : ‖x⁻¹‖ = ‖x‖⁻¹ := norm_inv x
  rw [hinvnorm] at hle_inv
  have hle' : ‖x‖ ≤ 1 :=
    (one_le_inv₀ hxnorm_pos).mp hle_inv
  exact le_antisymm hle' hle

theorem norm_j_gt_one_of_split (X : PuncturedEllipticCurve F)
    (h : X.HasSplitMultiplicativeReductionAt place) :
    1 < ‖(X.baseChange (Completion place)).jInvariant‖ :=
  LeanFormal.IUT.SourceTateParameter.norm_j_gt_one_of_splitMultiplicativeReductionAt X place h

/-! ### (ii) final: realization modulo `IsSquare γ` only -/

theorem split_realization_of_leanformal
    (X : PuncturedEllipticCurve F)
    (h : X.HasSplitMultiplicativeReductionAt place)
    (hEll : (X.curve.baseChange (Completion place)).IsElliptic)
    (hγ : IsSquare (TateCurvesTheta.gammaInvariant
      (X.curve.baseChange (Completion place)))) :
    ∃ (t : TateCurvesTheta.TateParameter (Completion place))
      (C : WeierstrassCurve.VariableChange (Completion place)),
      C • TateCurve.weierstrassCurve (Completion place) (t.q : Completion place) =
        (X.curve.baseChange (Completion place)) := by
  have h0 := norm_j_gt_one_of_split place X h
  haveI : (X.baseChange (Completion place)).curve.IsElliptic :=
    (X.baseChange (Completion place)).isElliptic
  rw [PuncturedEllipticCurve.jInvariant_spec] at h0
  exact leanformal_split_realization place X hEll h0 hγ

/-! ### Rows -/

def finalRows : List (String × String) :=
  [ ("(a) class valuation ↔ Valued.v on the completion", "PROVED (green re-export)"),
    ("(a) Valued.v x = 1 → ‖x‖ = 1", "PROVED"),
    ("(a) ‖j‖ > 1 from LeanFormal split predicate", "PROVED"),
    ("(b′) IsSquare γ from split predicate", "MISSING (Hensel-type lifting)"),
    ("(b) algebraic core IsSquare(-c4c6) ⟺ IsSquare γ", "PROVED (Mzk1SplitBridgeCompletionActual)"),
    ("(ii) realization modulo IsSquare γ only", "PROVED"),
    ("(iii) TatePointComparison point uniformization", "MISSING (analytic)") ]

theorem finalRows_length : finalRows.length = 7 := rfl

#check class_valuation_equiv_valued
#check norm_j_gt_one_of_split
#check split_realization_of_leanformal
#check finalRows_length

end LeanFormal.IUT.XiFPaper.Mzk1SplitBridgeFinalActual
end
