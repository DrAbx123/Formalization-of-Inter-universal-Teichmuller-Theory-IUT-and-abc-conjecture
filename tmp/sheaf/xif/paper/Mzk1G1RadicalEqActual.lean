import tmp.sheaf.xif.paper.Mzk1G1ABCCompactnessActual
import LeanFormal.IUT.ABCBridge.Statement
import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1RadicalEqActual
/-- The local G1 radical equals the standard ABCBridge radical. -/
theorem local_radical_eq_std (n : Nat) :
    Mzk1G1Actual.radical n = LeanFormal.IUT.radical n := by
  unfold Mzk1G1Actual.radical LeanFormal.IUT.radical LeanFormal.IUT.natRadical
  rw [Nat.radical_eq_prod_primeFactors]
  rfl
#print axioms local_radical_eq_std
end LeanFormal.IUT.XiFPaper.Mzk1G1RadicalEqActual
end