import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveNumericActual
/-- Cover degree of the Fermat cover `X^n+Y^n=Z^n`. -/
def fermatCoverDegree (n : Nat) : Nat := n ^ 2
theorem fermatCoverDegree_pos (hn : 0 < n) : 0 < fermatCoverDegree n := by
  unfold fermatCoverDegree; positivity
theorem fermatCoverDegree_eq (n : Nat) :
    fermatCoverDegree n = n * n := by
  unfold fermatCoverDegree; ring
/-- Log-different exponent for the Fermat cover. -/
def fermatDifferentExponent (n : Nat) : Nat := n ^ 2
theorem fermatDifferentExponent_nonneg (n : Nat) :
    0 ≤ fermatDifferentExponent n := by
  unfold fermatDifferentExponent; positivity
#print axioms fermatCoverDegree_pos
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveNumericActual
end