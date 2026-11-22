/- R5: conservative bound B(p,d) = d*(d+2) valid for all m <= d (route 7.1 L437).
No v_p monotonicity is used; padicValNat p d <= d is enough.
-/
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
namespace LeanFormal.IUT.XiFPaper.Mzk1G1DifferentBoundConservativeActual

/-- Conservative uniform different bound B(p,d)=d*(d+2). -/
def differentBoundConservative (d : ℕ) : ℕ := d * (d + 2)

/-- padicValNat p d <= d. -/
theorem padicValNat_le_self {p d : ℕ} [Fact p.Prime] :
    padicValNat p d ≤ d :=
  (padicValNat_le_nat_log d).trans (Nat.log_le_self p d)

/-- The Serre-style bound d*(v_p(d)+2) is at most the conservative d*(d+2). -/
theorem differentBound_le_conservative {p d : ℕ} [Fact p.Prime] :
    d * (padicValNat p d + 2) ≤ differentBoundConservative d := by
  unfold differentBoundConservative
  apply Nat.mul_le_mul_left
  exact Nat.add_le_add_right (padicValNat_le_self) 2

/-- Positivity for d > 0. -/
theorem differentBoundConservative_pos {d : ℕ} (hd : 0 < d) :
    0 < differentBoundConservative d := by
  unfold differentBoundConservative
  positivity

end LeanFormal.IUT.XiFPaper.Mzk1G1DifferentBoundConservativeActual
