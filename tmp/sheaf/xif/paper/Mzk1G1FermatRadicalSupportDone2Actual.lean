import tmp.sheaf.xif.paper.Mzk1G1EllipticHeightCriterionActual
import LeanFormal.IUT.ABCBridge.Statement
import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatRadicalSupportDone2Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
/-- The Frey conductor divides the ABC product. -/
theorem freyConductor_dvd_abc (a b c : Nat) :
    freyConductor a b c ∣ a * b * c := by
  rw [freyConductor_eq_radical]
  change LeanFormal.IUT.radical (a * b * c) ∣ a * b * c
  exact LeanFormal.IUT.radical_dvd_self
/-- The Frey conductor is positive. -/
theorem freyConductor_pos (a b c : Nat) : 0 < freyConductor a b c := by
  rw [freyConductor_eq_radical]
  change 0 < LeanFormal.IUT.radical (a * b * c)
  exact LeanFormal.IUT.radical_pos (a * b * c)
#print axioms freyConductor_dvd_abc
#print axioms freyConductor_pos
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatRadicalSupportDone2Actual
end