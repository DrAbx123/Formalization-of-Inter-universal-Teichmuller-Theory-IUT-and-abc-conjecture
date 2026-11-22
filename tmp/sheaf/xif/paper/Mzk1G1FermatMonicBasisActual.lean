/- G1-A Fermat monic basis rank restatement. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatChartRingActual2
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartRingActual2
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatMonicBasisActual
theorem fermatU0Basis_rank (n : Nat) (hn : 0 < n) :
    Module.finrank (Polynomial ℚ) (fermatU0Ring n) = n := by
  rw [Module.finrank_eq_card_basis (fermatU0Basis n hn)]
  rw [fermatU0Poly, Polynomial.natDegree_X_pow_sub_C]
  simp
theorem fermatU1Basis_rank (n : Nat) (hn : 0 < n) :
    Module.finrank (Polynomial ℚ) (fermatU1Ring n) = n := by
  rw [Module.finrank_eq_card_basis (fermatU1Basis n hn)]
  rw [fermatU1Poly, Polynomial.natDegree_X_pow_sub_C]
  simp
#print axioms fermatU0Basis_rank
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatMonicBasisActual
