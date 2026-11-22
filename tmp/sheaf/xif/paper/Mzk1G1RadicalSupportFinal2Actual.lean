import tmp.sheaf.xif.paper.Mzk1G1RadicalEqActual
import tmp.sheaf.xif.paper.Mzk1G1EllipticHeightCriterionActual
import LeanFormal.IUT.ABCBridge.Statement
import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1RadicalSupportFinal2Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
theorem freyConductor_eq_std_radical (a b c : Nat) :
    freyConductor a b c = LeanFormal.IUT.radical (a * b * c) := by
  rw [freyConductor_eq_radical]
  exact Mzk1G1RadicalEqActual.local_radical_eq_std (a * b * c)
theorem freyConductor_dvd_abc (a b c : Nat) : freyConductor a b c ∣ a * b * c := by
  rw [freyConductor_eq_std_radical]
  exact LeanFormal.IUT.radical_dvd_self
theorem freyConductor_pos (a b c : Nat) : 0 < freyConductor a b c := by
  rw [freyConductor_eq_std_radical]
  exact LeanFormal.IUT.radical_pos (a * b * c)
#print axioms freyConductor_dvd_abc
#print axioms freyConductor_pos
end LeanFormal.IUT.XiFPaper.Mzk1G1RadicalSupportFinal2Actual
end