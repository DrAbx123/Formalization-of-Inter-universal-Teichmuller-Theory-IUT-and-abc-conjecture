/- G1a Fermat canonical degree actual. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatCoverDataActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCoverDataActual
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatCanonicalDegreeActual
def canonicalDegree (n : Nat) : Rat := (n : Rat) - 3
theorem canonicalDegree_mul_ratio (n : Nat) (hn : 3 < n) :
    (fermatCoverData n (le_of_lt hn)).canonicalRatio * canonicalDegree n = (n : Rat) := by
  unfold fermatCoverData canonicalDegree
  have h : (n : Rat) - 3 ≠ 0 := by
    have hlt : (3 : Rat) < (n : Rat) := by exact_mod_cast hn
    linarith
  field_simp [h]
#print axioms canonicalDegree_mul_ratio
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatCanonicalDegreeActual
