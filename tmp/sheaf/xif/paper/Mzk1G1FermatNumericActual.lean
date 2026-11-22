/- G1a Fermat cover numeric data and arithmetic identities. -/
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatNumericActual
/-- Actual Fermat curve genus formula `(n(n-3))/2 + 1`, rational form. -/
def fermatGenus (n : ℚ) : ℚ := (n * (n - 3)) / 2 + 1
/-- Actual degree of `Y_n -> P^1` is `n^2`. -/
def fermatMapDegree (n : ℚ) : ℚ := n ^ 2
/-- Actual boundary divisor degree `#E = 3n`. -/
def fermatBoundaryDegree (n : ℚ) : ℚ := 3 * n
/-- Actual degree ratio `deg omega(E) / deg omega = n/(n-3)`. -/
def fermatCanonicalRatio (n : ℚ) : ℚ := n / (n - 3)
theorem fermat_genus_identity (n : ℚ) :
    2 * fermatGenus n - 2 = n * (n - 3) := by
  unfold fermatGenus
  ring
theorem fermat_mapDegree_identity (n : ℚ) :
    fermatMapDegree n = n * n := by
  unfold fermatMapDegree
  ring
theorem fermat_canonicalRatio_identity (n : ℚ) (hn : n ≠ 3) :
    fermatCanonicalRatio n = n / (n - 3) := by
  unfold fermatCanonicalRatio
  rfl
theorem fermat_boundary_identity (n : ℚ) :
    fermatBoundaryDegree n = 3 * n := rfl
#print axioms fermat_genus_identity
#print axioms fermat_canonicalRatio_identity
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatNumericActual
