/- G1a Fermat numeric data structure (small). -/
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatNumericDataActual
structure FermatNumericData where
  n : ℕ
  genus : ℚ
  mapDegree : ℚ
  boundary : ℚ
  canonicalRatio : ℚ
noncomputable def fermatNumericData (n : ℕ) : FermatNumericData where
  n := n
  genus := ((n : ℚ) * ((n : ℚ) - 3)) / 2 + 1
  mapDegree := (n : ℚ) ^ 2
  boundary := 3 * (n : ℚ)
  canonicalRatio := (n : ℚ) / ((n : ℚ) - 3)
theorem fermatNumericData_genus_identity (n : ℕ) :
    2 * (fermatNumericData n).genus - 2 = (n : ℚ) * ((n : ℚ) - 3) := by
  unfold fermatNumericData; ring
theorem fermatNumericData_degree_identity (n : ℕ) :
    (fermatNumericData n).mapDegree = (n : ℚ) * n := by
  unfold fermatNumericData; ring
#print axioms fermatNumericData_genus_identity
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatNumericDataActual
