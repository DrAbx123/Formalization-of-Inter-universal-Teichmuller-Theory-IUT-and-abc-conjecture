import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# S2481 index equality

For rational numbers `q r`, clearing the denominators occurring in the
candidate inverse map `S2481ReverseRat` gives the integer identity

  ((q.den * r.den) / (q + r).den) * (q + r).num
    = ((q.den * r.den) / q.den) * q.num + ((q.den * r.den) / r.den) * r.num.

Equivalently, with `N = q.den * r.den`, the three indices
`N / (q + r).den`, `N / q.den`, `N / r.den` satisfy the linear relation
needed for the additivity of `S2481ReverseRat`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2481CoeffLimitActual

/-- The denominator-clearing index identity behind the additivity of
`S2481ReverseRat`. -/
theorem S2481_index_eq (q r : ℚ) :
    let N : ℕ := (q.pnatDen : ℕ) * (r.pnatDen : ℕ)
    let a : ℕ := N / ((q + r).pnatDen : ℕ)
    let b : ℕ := N / (q.pnatDen : ℕ)
    let c : ℕ := N / (r.pnatDen : ℕ)
    (a : ℤ) * (q + r).num = (b : ℤ) * q.num + (c : ℤ) * r.num := by
  dsimp only
  simp only [Rat.coe_pnatDen]
  set D : ℕ := q.den * r.den with hD
  have hdvd : (q + r).den ∣ D := by
    rw [hD]
    exact Rat.add_den_dvd q r
  have hB0 : ((q + r).den : ℤ) ≠ 0 := by
    exact_mod_cast (q + r).den_ne_zero
  -- `D = (q + r).den * a`, hence multiplying by `(q + r).den` recovers `D`.
  have ha : ((D / (q + r).den : ℕ) : ℤ) * ((q + r).den : ℤ) = (D : ℤ) := by
    have h := Nat.div_mul_cancel hdvd
    rw [← Nat.cast_mul, h]
  -- The cross-multiplied form of `Rat.add_num_den'`.
  have hz : ((q + r).num : ℤ) * (D : ℤ) =
      (q.num * (r.den : ℤ) + r.num * (q.den : ℤ)) * ((q + r).den : ℤ) := by
    have h := Rat.add_num_den' q r
    rw [hD, Nat.cast_mul]
    calc
      ((q + r).num : ℤ) * ((q.den : ℤ) * (r.den : ℤ))
          = (q + r).num * (q.den : ℤ) * (r.den : ℤ) := by ring
      _ = (q.num * (r.den : ℤ) + r.num * (q.den : ℤ)) * ((q + r).den : ℤ) := h
  -- Cancel the nonzero denominator after multiplying the desired identity by it.
  have hkey : ((D / (q + r).den : ℕ) : ℤ) * (q + r).num =
      q.num * (r.den : ℤ) + r.num * (q.den : ℤ) := by
    apply mul_right_cancel₀ hB0
    calc
      (((D / (q + r).den : ℕ) : ℤ) * (q + r).num) * ((q + r).den : ℤ)
          = ((D / (q + r).den : ℕ) : ℤ) *
              ((q + r).num * ((q + r).den : ℤ)) := by ring
      _ = ((D / (q + r).den : ℕ) : ℤ) *
              (((q + r).den : ℤ) * (q + r).num) := by ring
      _ = (((D / (q + r).den : ℕ) : ℤ) * ((q + r).den : ℤ)) *
              (q + r).num := by ring
      _ = (D : ℤ) * (q + r).num := by rw [ha]
      _ = ((q + r).num : ℤ) * (D : ℤ) := by ring
      _ = (q.num * (r.den : ℤ) + r.num * (q.den : ℤ)) * ((q + r).den : ℤ) := hz
  have hb : D / q.den = r.den := by
    rw [hD]
    exact Nat.mul_div_right r.den q.pos
  have hc : D / r.den = q.den := by
    rw [hD]
    exact Nat.mul_div_left q.den r.pos
  rw [hkey, hb, hc]
  ring

end LeanFormal.IUT.XiFPaper.S2481CoeffLimitActual
