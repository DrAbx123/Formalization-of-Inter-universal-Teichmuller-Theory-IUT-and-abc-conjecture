/- G1a cover final2. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatCoverFinalActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCoverDataActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCoverFinalActual
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatCoverFinal2Actual
theorem fermatCoverFinal2 (n : Nat) (hn : 3 ≤ n) :
    (fermatCoverData n hn).degree = (n : Rat) ^ 2 ∧
    (fermatCoverData n hn).boundaryDegree = 3 * (n : Rat) := by
  exact ⟨fermatCover_degree_formula n hn, fermatCover_boundary_formula n hn⟩
#print axioms fermatCoverFinal2
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatCoverFinal2Actual
