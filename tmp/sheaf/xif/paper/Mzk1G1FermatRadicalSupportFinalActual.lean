/- G1a radical support final actual. -/
import tmp.sheaf.xif.paper.Mzk1G1ABCCompactnessActual
import tmp.sheaf.xif.paper.Mzk1G1EllipticHeightCriterionActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatRadicalSupportFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
theorem radical_dvd_self_final (n : Nat) : radical n ∣ n := by
  by_cases hn : n = 0
  · subst hn; simp [radical]
  · unfold radical
    rw [← Nat.prod_primeFactorsList hn]
    exact (n.primeFactorsList : Multiset Nat).toFinset_prod_dvd_prod
theorem radical_pos_final (n : Nat) : 0 < radical n := by
  unfold radical
  exact Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactorsList (List.mem_toFinset.mp hp)).pos)
theorem freyConductor_dvd_abc_final (a b c : Nat) : freyConductor a b c ∣ a * b * c := by
  rw [freyConductor_eq_radical]; exact radical_dvd_self_final (a * b * c)
theorem freyConductor_pos_final (a b c : Nat) : 0 < freyConductor a b c := by
  rw [freyConductor_eq_radical]; exact radical_pos_final (a * b * c)
#print axioms freyConductor_dvd_abc_final
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatRadicalSupportFinalActual
