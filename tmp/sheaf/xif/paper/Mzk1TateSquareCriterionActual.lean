/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1TateInstanceCoherenceActual
import TateCurvesTheta.Converse.ReductionType
import Mathlib.Tactic

/-! # Mzk1TateSquareCriterionActual — square criterion and split-case realization (A820, qpilot)

Results:
1. `isSquare_gamma_div_of_split`: for two curves both with vendor split multiplicative
   reduction, `γ(W₂)/γ(W₁)` is a square (quotient of the squares supplied by
   `hasSplitMultiplicativeReduction_iff`).
2. `split_realization_canonical`: if `W` (over the completion) has vendor split
   multiplicative reduction, then `W` is realized by a *canonical LeanFormal Tate curve*
   at the correct vendor parameter `t`: there is `C` with `C • canonical(t.q) = W`.
   This is the base-level realization (ii) for the correct q, using the vendor theorem
   `hasSplitMultiplicativeReduction_iff_exists_tateCurve` plus the instance-coherent
   `tateCurve_eq'` and the inversion of the variable change.
3. **Semantic correction**: the realization holds at the *vendor Tate parameter* `t.q`
   (or `Some` curve with split reduction), NOT at an arbitrary `FinitePlaceQCandidate`;
   an arbitrary candidate's canonical curve has no reason to realize `W`.  Hence
   `tateComparisonDataOfCandidate` cannot be filled for an arbitrary candidate; the
   correct statement is the one in (2), and the remaining bridge is the predicate
   implication `LeanFormal HasSplitMultiplicativeReductionAt ⇒ vendor
   HasSplitMultiplicativeReduction` (minimal-model class vs vendor integral-model predicate).
4. (iii) stays PENDING (analytic point uniformization), not faked.

No axiom, no sorry, no `True` placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1TateSquareCriterionActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1TateInstanceCoherenceActual

/-! ### 1. Quotient of squares -/

theorem isSquare_div_of_isSquare {K : Type*} [Field K] {a b : K}
    (ha : IsSquare a) (hb : IsSquare b) : IsSquare (a / b) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  by_cases hy : y = 0
  · subst hy
    simp
  · refine ⟨x / y, ?_⟩
    field_simp

/-! ### 2. Both split ⇒ γ-ratio is a square -/

section SquareCriterion

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem isSquare_gamma_div_of_split
    (W₁ W₂ : WeierstrassCurve K) [W₁.IsElliptic] [W₂.IsElliptic]
    (h12 : (12 : K) ≠ 0)
    (h₁ : TateCurvesTheta.HasSplitMultiplicativeReduction W₁)
    (h₂ : TateCurvesTheta.HasSplitMultiplicativeReduction W₂) :
    IsSquare (TateCurvesTheta.gammaInvariant W₂ / TateCurvesTheta.gammaInvariant W₁) := by
  have hγ₁ : IsSquare (TateCurvesTheta.gammaInvariant W₁) :=
    ((TateCurvesTheta.hasSplitMultiplicativeReduction_iff h12 W₁).mp h₁).2
  have hγ₂ : IsSquare (TateCurvesTheta.gammaInvariant W₂) :=
    ((TateCurvesTheta.hasSplitMultiplicativeReduction_iff h12 W₂).mp h₂).2
  exact isSquare_div_of_isSquare hγ₂ hγ₁

/-- The canonical-side square fact: for a vendor Tate parameter, `γ(t.tateCurve)` is a
square. -/
theorem isSquare_gamma_tateCurve
    (t : TateCurvesTheta.TateParameter K) (h12 : (12 : K) ≠ 0) :
    IsSquare (TateCurvesTheta.gammaInvariant t.tateCurve) := by
  haveI := t.tateCurve_isElliptic h12
  exact ((TateCurvesTheta.hasSplitMultiplicativeReduction_iff h12 t.tateCurve).mp
    (t.hasSplitMultiplicativeReduction h12)).2

end SquareCriterion

/-! ### 3. Split-case realization by a canonical LeanFormal Tate curve -/

variable {F : Type*} [Field F] [NumberField F]
variable (place : NumberField.FinitePlace F)
variable [IsUltrametricDist (Completion place)] [CompleteSpace (Completion place)]

/-- **Split-case realization (correct q)**: a curve over the completion with vendor split
multiplicative reduction is obtained from a canonical LeanFormal Tate curve by a variable
change over the completion.  The Tate parameter is the vendor one; no claim is made about
arbitrary q-candidates. -/
theorem split_realization_canonical
    (W : WeierstrassCurve (Completion place)) [W.IsElliptic]
    (hW : TateCurvesTheta.HasSplitMultiplicativeReduction W) :
    ∃ (t : TateCurvesTheta.TateParameter (Completion place))
      (C : WeierstrassCurve.VariableChange (Completion place)),
      C • TateCurve.weierstrassCurve (Completion place) (t.q : Completion place) = W := by
  have h12 : (12 : Completion place) ≠ 0 := by
    haveI := Mzk1TateInstanceCoherenceActual.completionCharZero place
    norm_num
  obtain ⟨t, C, hC⟩ :=
    (TateCurvesTheta.hasSplitMultiplicativeReduction_iff_exists_tateCurve h12 W).mp hW
  refine ⟨t, C⁻¹, ?_⟩
  rw [← Mzk1TateInstanceCoherenceActual.tateCurve_eq' t]
  have := congrArg (fun V => C⁻¹ • V) hC
  simpa only [inv_smul_smul] using this.symm

/-! ### 4. Rows -/

def squareCriterionRows : List (String × String) :=
  [ ("quotient of two squares is a square", "PROVED"),
    ("both split multiplicative ⇒ IsSquare (γ W₂ / γ W₁)", "PROVED"),
    ("canonical Tate curve has square γ", "PROVED"),
    ("split curve realized by a canonical LeanFormal Tate curve (correct q)", "PROVED (conditional on vendor split predicate)"),
    ("realization at arbitrary FinitePlaceQCandidate", "FALSE in general (semantic correction)"),
    ("predicate bridge LeanFormal HasSplitMultiplicativeReductionAt ⇒ vendor predicate", "MISSING"),
    ("(iii) TatePointComparison point uniformization", "MISSING (analytic)") ]

theorem squareCriterionRows_length : squareCriterionRows.length = 7 := rfl

#check isSquare_gamma_div_of_split
#check split_realization_canonical
#check squareCriterionRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TateSquareCriterionActual
end
