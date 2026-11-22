import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatRamificationActual
/-- Tame ramification index of the Fermat cover at a point. -/
def fermatRamificationIndex (n : Nat) : Nat := n
theorem fermatRamificationIndex_pos (hn : 0 < n) :
    0 < fermatRamificationIndex n := hn
/-- Reduction of the Fermat cover at a prime. -/
def fermatReductionMod (n p : Nat) : Prop := p ∣ n
theorem fermatReductionMod_iff (n p : Nat) :
    fermatReductionMod n p ↔ p ∣ n := Iff.rfl
#print axioms fermatRamificationIndex_pos
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatRamificationActual
end