/- U-C D2 second form: elementary corollaries (light file, no heavy imports).

Consumers of D2SecondForm (D2V2Skeleton assembly, D4Inputs) often need Q >= 0 or
the decomposition h = Q + (h - Q); these follow immediately from the structure
fields (h_nonneg, Cd_nonneg, h_sub_Q_nonneg, h_sub_Q_le, Q_le_h).
-/
import tmp.sheaf.xif.paper.Mzk1ULD2SecondFormActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULD2SecondFormCorollariesActual

open LeanFormal.IUT.XiFPaper.Mzk1ULD2SecondFormActual

/-- PROVED: Q <= h (re-export). -/
theorem D2SecondForm.Q_le_h' (D : D2SecondForm) : D.Q ≤ D.h :=
  D.Q_le_h

/-- PROVED: the decomposition h = Q + (h - Q). -/
theorem D2SecondForm.h_eq (D : D2SecondForm) : D.h = D.Q + (D.h - D.Q) := by
  ring

end LeanFormal.IUT.XiFPaper.Mzk1ULD2SecondFormCorollariesActual
end