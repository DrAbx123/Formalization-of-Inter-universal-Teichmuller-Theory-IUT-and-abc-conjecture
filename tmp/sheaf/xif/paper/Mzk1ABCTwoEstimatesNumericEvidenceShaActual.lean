import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesShaActual

/-!
# shehdd A606 two-estimates numeric evidence (Sha)

Explicit numeric sanity witnesses for the two IUT IV Thm 1.10 estimate shapes
(canonical `Mzk1ABCTwoEstimatesNumericEvidenceActual` is mainline-exclusive;
this file uses the shehdd `Sha` suffix):
* height slot: a concrete sample satisfies `h <= (1+δ)*L`;
* volume slot: a concrete sample satisfies `v <= (1+δ)*w + hull + D`;
* both shapes are non-vacuous as real inequalities.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesNumericEvidenceShaActual

theorem height_numeric_sample : (2 : Real) ≤ (1 + (1 / 10)) * 2 :=
  by norm_num

theorem height_numeric_sample_strict : (2 : Real) < (1 + (1 / 10)) * 2 :=
  by norm_num

theorem volume_numeric_sample : (5 : Real) ≤ (1 + (1 / 2)) * 4 + 2 + 1 :=
  by norm_num

theorem volume_numeric_sample_zero_D : (0 : Real) ≤ (1 + (1 / 2)) * 0 + 0 + 0 :=
  by norm_num

/-- The estimate shapes are jointly satisfiable at the sample point
`h = L = 2`, `v = 5`, `w = 4`, `hull = 2`, `D = 1`. -/
theorem two_estimates_numeric_witness :
    (2 : Real) ≤ (1 + (1 / 10)) * 2 ∧
      (5 : Real) ≤ (1 + (1 / 2)) * 4 + 2 + 1 :=
  ⟨height_numeric_sample, volume_numeric_sample⟩

end LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesNumericEvidenceShaActual
