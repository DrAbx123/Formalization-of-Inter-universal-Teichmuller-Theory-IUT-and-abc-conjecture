import tmp.sheaf.xif.paper.Mzk1G1FermatCurveNumericActual
import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatTraceActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveNumericActual
/-- Trace degree of the Fermat cover. -/
def fermatTraceDegree (n : Nat) : Nat := fermatCoverDegree n
theorem fermatTraceDegree_pos (hn : 0 < n) :
    0 < fermatTraceDegree n := fermatCoverDegree_pos hn
theorem fermatTraceDegree_eq (n : Nat) : fermatTraceDegree n = n ^ 2 := rfl
#print axioms fermatTraceDegree_pos
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatTraceActual
end