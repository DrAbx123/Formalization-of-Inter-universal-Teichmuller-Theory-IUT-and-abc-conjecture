import tmp.sheaf.xif.paper.Mzk1G1CriterionAllActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual

/-- Actual conversion: an ABC elliptic-height criterion gives Frey height
bound data. -/
def freyHeightOfCriterion {ε : ℝ} (D : ABCEllipticHeightCriterion ε) :
    FreyHeightBound ε where
  C := D.C
  C_nonneg := D.C_nonneg
  height_ineq := D.height_ineq

/-- Actual equivalence of the two presentations at each ε. -/
theorem freyHeightBound_iff_criterion (ε : ℝ) :
    Nonempty (FreyHeightBound ε) ↔ Nonempty (ABCEllipticHeightCriterion ε) := by
  constructor
  · rintro ⟨H⟩
    exact ⟨criterionOfFreyHeight H⟩
  · rintro ⟨D⟩
    exact ⟨freyHeightOfCriterion D⟩

/-- Actual all-ε equivalence. -/
theorem freyHeightBoundAll_iff_criterionAll :
    (∀ ε : ℝ, 0 < ε → Nonempty (FreyHeightBound ε)) ↔
      ABCEllipticHeightCriterionAll := by
  constructor
  · intro H ε hε
    exact (freyHeightBound_iff_criterion ε).mp (H ε hε)
  · intro H ε hε
    exact (freyHeightBound_iff_criterion ε).mpr (H ε hε)

end LeanFormal.IUT.XiFPaper.Mzk1G1Actual
end
