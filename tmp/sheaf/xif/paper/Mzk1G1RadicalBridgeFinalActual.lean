import tmp.sheaf.xif.paper.Mzk1G1EllipticHeightCriterionActual
import LeanFormal.IUT.ABCBridge.Statement
import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1RadicalBridgeFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
theorem radicalBridge_eq (a b c : Nat) :
    freyConductor a b c = radical (a * b * c) := freyConductor_eq_radical a b c
theorem radicalBridge_dvd (a b c : Nat) :
    freyConductor a b c ∣ a * b * c := by
  rw [radicalBridge_eq]
  change LeanFormal.IUT.radical (a * b * c) ∣ a * b * c
  exact LeanFormal.IUT.radical_dvd_self
theorem radicalBridge_pos (a b c : Nat) : 0 < freyConductor a b c := by
  rw [radicalBridge_eq]
  change 0 < LeanFormal.IUT.radical (a * b * c)
  exact LeanFormal.IUT.radical_pos (a * b * c)
#print axioms radicalBridge_dvd
end LeanFormal.IUT.XiFPaper.Mzk1G1RadicalBridgeFinalActual
end