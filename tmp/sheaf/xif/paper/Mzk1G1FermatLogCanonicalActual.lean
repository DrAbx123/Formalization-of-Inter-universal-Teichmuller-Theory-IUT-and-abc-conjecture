import tmp.sheaf.xif.paper.Mzk1G1FermatCurveNumericActual
import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatLogCanonicalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveNumericActual
/-- Log-canonical degree of the Fermat cover. -/
def fermatLogCanonicalDegree (n : Nat) : Nat := fermatCoverDegree n
theorem fermatLogCanonicalDegree_eq (n : Nat) :
    fermatLogCanonicalDegree n = fermatCoverDegree n := rfl
theorem fermatLogCanonicalDegree_pos (hn : 0 < n) :
    0 < fermatLogCanonicalDegree n := fermatCoverDegree_pos hn
#print axioms fermatLogCanonicalDegree_pos
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatLogCanonicalActual
end