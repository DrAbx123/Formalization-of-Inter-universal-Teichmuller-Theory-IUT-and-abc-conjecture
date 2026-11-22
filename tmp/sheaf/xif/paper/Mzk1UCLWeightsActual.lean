import tmp.sheaf.xif.paper.Mzk1P6WeightedPacketHullActual
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1UCLWeightsActual
variable (n : Nat)
/-- Actual U-L StepV index set. -/
abbrev ULIndex : Type := {j : Nat // j ∈ Finset.Icc 1 n}
/-- Actual uniform StepV weights 1/n. -/
noncomputable def uLWeight : ULIndex n → Real := fun _ => 1 / (n : Real)
theorem uLWeight_nonneg (hn : 0 < n) (i : ULIndex n) : 0 ≤ uLWeight n i := by
  unfold uLWeight
  positivity
theorem uLWeight_sum (hn : 0 < n) :
    (∑ i : ULIndex n, uLWeight n i) = 1 := by
  unfold uLWeight
  rw [Finset.sum_const, Finset.univ_eq_attach, Finset.card_attach]
  have hcard : (Finset.Icc 1 n).card = n := by
    rw [Nat.card_Icc]
    omega
  rw [hcard, nsmul_eq_mul]
  have hn' : (n : Real) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
#print axioms uLWeight_sum
end LeanFormal.IUT.XiFPaper.Mzk1UCLWeightsActual
end
