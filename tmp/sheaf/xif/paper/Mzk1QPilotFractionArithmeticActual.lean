/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # q-pilot: rational fraction arithmetic (q < 1 power decay) -/

namespace LeanFormal.IUT.XiFPaper.QPilotFractionArithmeticActual

theorem qpow_pos {q : ℚ} (hq : 0 < q) (n : Nat) : 0 < q ^ n := pow_pos hq n

theorem qpow_succ_lt {q : ℚ} (hq0 : 0 < q) (hq1 : q < 1) (n : Nat) :
    q ^ (n + 1) < q ^ n := by
  rw [pow_succ]
  have h := (mul_lt_mul_left (qpow_pos hq0 n)).mpr hq1
  simpa using h

theorem qpow_lt_qpow_of_lt {q : ℚ} (hq0 : 0 < q) (hq1 : q < 1) {m n : Nat}
    (h : m < n) : q ^ n < q ^ m := by
  induction h with
  | refl =>
      rw [pow_succ]
      have hstep := qpow_succ_lt hq0 hq1 _
      exact hstep
  | step hnm ih =>
      calc q ^ (Nat.succ _) = q ^ _ * q := pow_succ _ _
        _ < q ^ _ := by
            have hp : 0 < q ^ _ := qpow_pos hq0 _
            have hlt := (mul_lt_mul_left hp).mpr hq1
            simpa using hlt
        _ < q ^ m := ih

theorem qpow_lt_one {q : ℚ} (hq0 : 0 < q) (hq1 : q < 1) {n : Nat} (hn : 0 < n) :
    q ^ n < 1 := by
  have h := (qpow_lt_qpow_of_lt hq0 hq1 hn).trans_le ?_
  · exact h
  · simp

end LeanFormal.IUT.XiFPaper.QPilotFractionArithmeticActual
