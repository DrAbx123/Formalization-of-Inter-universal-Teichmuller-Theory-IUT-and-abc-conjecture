import tmp.sheaf.xif.paper.Mzk1G1EllipticHeightCriterionActual
import LeanFormal.IUT.ABCBridge.Statement
import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatRadicalSupportDoneActual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual in
theorem radical_dvd_self_actual (n : Nat) :
    LeanFormal.IUT.XiFPaper.Mzk1G1Actual.radical n ∣ n := by
  by_cases hn : n = 0
  · subst hn
    simp [LeanFormal.IUT.XiFPaper.Mzk1G1Actual.radical]
  · rw [← Nat.prod_primeFactorsList hn]
    exact (n.primeFactorsList : Multiset Nat).toFinset_prod_dvd_prod
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual in
theorem radical_pos_actual (n : Nat) :
    0 < LeanFormal.IUT.XiFPaper.Mzk1G1Actual.radical n := by
  unfold LeanFormal.IUT.XiFPaper.Mzk1G1Actual.radical
  exact Finset.prod_pos (fun p hp =>
    (Nat.prime_of_mem_primeFactorsList (List.mem_toFinset.mp hp)).pos)

/-- The Frey conductor divides the ABC product. -/
theorem freyConductor_dvd_abc (a b c : Nat) :
    freyConductor a b c ∣ a * b * c := by
  rw [freyConductor_eq_radical]
  exact radical_dvd_self_actual (a * b * c)
/-- The Frey conductor is positive. -/
theorem freyConductor_pos (a b c : Nat) : 0 < freyConductor a b c := by
  rw [freyConductor_eq_radical]
  exact radical_pos_actual (a * b * c)
#print axioms freyConductor_dvd_abc
#print axioms freyConductor_pos
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatRadicalSupportDoneActual
end