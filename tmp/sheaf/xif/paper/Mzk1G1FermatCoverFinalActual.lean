/- G1a Fermat cover final numeric assembly. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatCoverDataActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCoverDataActual
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatCoverFinalActual
theorem fermatCover_degree_formula (n : ℕ) (hn : 3 ≤ n) :
    (fermatCoverData n hn).degree = (n : ℚ) ^ 2 := rfl
theorem fermatCover_ramification_formula (n : ℕ) (hn : 3 ≤ n) :
    (fermatCoverData n hn).ramification = (n : ℚ) := rfl
theorem fermatCover_boundary_formula (n : ℕ) (hn : 3 ≤ n) :
    (fermatCoverData n hn).boundaryDegree = 3 * (n : ℚ) := rfl
theorem fermatCover_canonicalRatio_formula (n : ℕ) (hn : 3 ≤ n) :
    (fermatCoverData n hn).canonicalRatio = (n : ℚ) / ((n : ℚ) - 3) := rfl
theorem fermatCover_all_formulas (n : ℕ) (hn : 3 ≤ n) :
    2 * (fermatCoverData n hn).genus - 2 = (n : ℚ) * ((n : ℚ) - 3) ∧
    (fermatCoverData n hn).degree = (n : ℚ) ^ 2 ∧
    (fermatCoverData n hn).boundaryDegree = 3 * (n : ℚ) :=
  ⟨by unfold fermatCoverData; ring, rfl, rfl⟩
#print axioms fermatCover_all_formulas
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatCoverFinalActual
