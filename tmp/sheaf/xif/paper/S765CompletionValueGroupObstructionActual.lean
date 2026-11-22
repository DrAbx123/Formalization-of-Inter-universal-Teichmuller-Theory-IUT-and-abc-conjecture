import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-! # S765: completion value-group obstruction for a 2l-th root

If lambda is a completion element whose 2l-th power is q, and v(q)=order in
the value group, then 2l * v(lambda) = order; hence 2l divides order.
For paper q with order coprime to l (and order odd), this is impossible.
No completion root is constructed; this is the exact no-go. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S765CompletionValueGroupObstructionActual

/-- Integer value-group equation for a completion 2l-th root. -/
theorem twoL_mul_valuation_eq_order_implies_dvd
    {order : Nat} {l : Nat} {r : Int}
    (h : (2 * (l : Int)) * r = (order : Int)) :
    (2 * l) ∣ order := by
  exact Int.ofNat_dvd.mpr ⟨r, by simpa [Int.natCast_mul] using h.symm⟩

/-- No completion 2l-th root when 2l does not divide the order. -/
theorem no_completion_twoL_root_of_not_dvd
    {order : Nat} {l : Nat} {r : Int}
    (hnot : ¬ (2 * l) ∣ order)
    (h : (2 * (l : Int)) * r = (order : Int)) : False :=
  hnot (twoL_mul_valuation_eq_order_implies_dvd h)

/-- Paper order is coprime to l, so 2l cannot divide order (order odd). -/
theorem not_twoL_dvd_order_of_coprime
    {l order : Nat} (hl : 0 < l) (hcop : Nat.Coprime order l) (hodd : Odd order) :
    ¬ (2 * l) ∣ order := by
  intro hdvd
  have h2 : 2 ∣ order := dvd_trans (by omega : 2 ∣ 2 * l) hdvd
  have hnot2 : ¬ 2 ∣ order := Nat.not_even_iff_odd.mpr hodd
  exact hnot2 h2

/-- Exact no-go: a completion root forces 2l | order, contradicting paper
coprimality/oddness. -/
theorem completion_twoL_root_impossible
    {l order : Nat} (hl : 0 < l) (hcop : Nat.Coprime order l) (hodd : Odd order)
    {r : Int} (h : (2 * (l : Int)) * r = (order : Int)) : False :=
  no_completion_twoL_root_of_not_dvd
    (not_twoL_dvd_order_of_coprime hl hcop hodd) h

end LeanFormal.IUT.XiFPaper.S765CompletionValueGroupObstructionActual

end
