/- G1a Fermat cover arithmetic identities (small). -/
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatArithActual
def fermatGenus (n : ℚ) : ℚ := (n * (n - 3)) / 2 + 1
def fermatEuler (n : ℚ) : ℚ := 2 - 2 * fermatGenus n
def fermatMapDegree (n : ℚ) : ℚ := n ^ 2
def fermatBoundary (n : ℚ) : ℚ := 3 * n
def fermatCanonicalRatio (n : ℚ) : ℚ := n / (n - 3)
theorem fermat_genus_identity (n : ℚ) : 2 * fermatGenus n - 2 = n * (n - 3) := by
  unfold fermatGenus; ring
theorem fermat_euler_identity (n : ℚ) : fermatEuler n = -n * (n - 3) := by
  unfold fermatEuler fermatGenus; ring
theorem fermat_degree_identity (n : ℚ) : fermatMapDegree n = n * n := by
  unfold fermatMapDegree; ring
theorem fermat_boundary_identity (n : ℚ) : fermatBoundary n = 3 * n := rfl
theorem fermat_canonicalRatio_identity (n : ℚ) (hn : n ≠ 3) :
    fermatCanonicalRatio n = n / (n - 3) := rfl
#print axioms fermat_genus_identity
#print axioms fermat_canonicalRatio_identity
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatArithActual
