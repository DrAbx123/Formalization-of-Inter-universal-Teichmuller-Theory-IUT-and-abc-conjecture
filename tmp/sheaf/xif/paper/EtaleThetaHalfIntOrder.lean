import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntOrder

abbrev HalfInt : Type := Rat

def halfInt (n : Int) : HalfInt := (n : Rat) / 2

theorem halfInt_le_iff {n m : Int} :
    halfInt n <= halfInt m ↔ n <= m := by
  unfold halfInt
  constructor
  · intro h
    have h2 : (n : Rat) <= (m : Rat) := by linarith
    exact_mod_cast h2
  · intro h
    have h2 : (n : Rat) <= (m : Rat) := by exact_mod_cast h
    linarith

theorem halfInt_lt_iff {n m : Int} :
    halfInt n < halfInt m ↔ n < m := by
  unfold halfInt
  constructor
  · intro h
    have h2 : (n : Rat) < (m : Rat) := by linarith
    exact_mod_cast h2
  · intro h
    have h2 : (n : Rat) < (m : Rat) := by exact_mod_cast h
    linarith

#check halfInt_le_iff
#check halfInt_lt_iff

end LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntOrder
