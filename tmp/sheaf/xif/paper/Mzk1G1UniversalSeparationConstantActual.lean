/- Route 7.2: the explicit uniform different bound B = d * (v_p(d) + 1) and the resulting
positive separation constant p^{-B}. -/
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1UniversalSeparationConstantActual

/-- The explicit different bound depending only on p and d. -/
def differentBound (p d : Nat) : Nat := d * (padicValNat p d + 1)

theorem differentBound_nonneg (p d : Nat) : 0 ≤ differentBound p d := Nat.zero_le _

/-- Positive degree gives a positive different bound. -/
theorem differentBound_pos {p d : Nat} (hd : 0 < d) : 0 < differentBound p d := by
  unfold differentBound
  exact Nat.mul_pos hd (Nat.succ_pos _)

/-- The separation constant p^{-B} is positive. -/
theorem separationConstant_pos {p : Nat} [Fact p.Prime] (d : Nat) :
    (0 : ℝ) < (p : ℝ) ^ (-(differentBound p d : ℤ)) :=
  zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _

/-- The separation constant p^{-B} is at most one. -/
theorem separationConstant_le_one {p : Nat} [Fact p.Prime] (d : Nat) :
    (p : ℝ) ^ (-(differentBound p d : ℤ)) ≤ 1 := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_le
  have h : (-(differentBound p d : ℤ)) ≤ 0 := by omega
  exact zpow_le_one_of_nonpos₀ hp1 h

#print axioms differentBound_pos
#print axioms separationConstant_pos
#print axioms separationConstant_le_one
end LeanFormal.IUT.XiFPaper.Mzk1G1UniversalSeparationConstantActual
