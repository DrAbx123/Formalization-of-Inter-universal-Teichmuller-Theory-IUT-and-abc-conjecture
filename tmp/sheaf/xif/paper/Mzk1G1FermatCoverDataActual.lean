/- G1a Fermat cover data structure (small). -/
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatCoverDataActual
structure FermatCoverData where
  n : ℕ
  hn : 3 ≤ n
  degree : ℚ
  ramification : ℚ
  genus : ℚ
  boundaryDegree : ℚ
  canonicalRatio : ℚ
noncomputable def fermatCoverData (n : ℕ) (hn : 3 ≤ n) : FermatCoverData where
  n := n
  hn := hn
  degree := (n : ℚ) ^ 2
  ramification := n
  genus := ((n : ℚ) * ((n : ℚ) - 3)) / 2 + 1
  boundaryDegree := 3 * (n : ℚ)
  canonicalRatio := (n : ℚ) / ((n : ℚ) - 3)
theorem fermatCoverData_RH (n : ℕ) (hn : 3 ≤ n) :
    2 * (fermatCoverData n hn).genus - 2 = (n : ℚ) * ((n : ℚ) - 3) := by
  unfold fermatCoverData; ring
#print axioms fermatCoverData_RH
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatCoverDataActual
