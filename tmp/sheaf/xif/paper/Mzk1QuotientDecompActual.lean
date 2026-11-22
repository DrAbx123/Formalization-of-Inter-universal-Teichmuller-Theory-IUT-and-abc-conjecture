/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic
/-! # Division cancellation in the torsion-index decomposition -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1QuotientDecompActual
/-- Cancel the p-power torsion factor and `T0` from the quotient index. -/
theorem quotient_decomp
    {p q f A m T0 T : Nat} (hp : 0 < p) (hT0pos : 0 < T0)
    (hq : q = p ^ f) (hT : T = p ^ m * T0)
    (hT0 : T0 ∣ q - 1) (hm : m ≤ f * A) :
    q ^ A * (q - 1) / T = p ^ (f * A - m) * ((q - 1) / T0) := by
  obtain ⟨c, hc⟩ := hT0
  rw [hT, hc, hq, ← pow_mul]
  have hpow : p ^ (f * A) = p ^ (f * A - m) * p ^ m := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hTc : T0 * c / T0 = c :=
    Nat.mul_div_right c hT0pos
  rw [hTc]
  calc
    p ^ (f * A) * (T0 * c) / (p ^ m * T0)
        = p ^ (f * A) * c / p ^ m := by
          rw [show p ^ (f * A) * (T0 * c) = (p ^ (f * A) * c) * T0 by ring]
          rw [show p ^ m * T0 = p ^ m * T0 from rfl]
          exact Nat.mul_div_mul_right (p ^ (f * A) * c) (p ^ m) hT0pos
    _ = p ^ (f * A - m) * c := by
          rw [hpow]
          have hdiv : (p ^ (f * A - m) * p ^ m * c) / p ^ m =
              p ^ (f * A - m) * c := by
            rw [mul_comm (p ^ (f * A - m)) (p ^ m), mul_assoc]
            exact Nat.mul_div_right (p ^ (f * A - m) * c) (pow_pos hp m)
          exact hdiv
end LeanFormal.IUT.XiFPaper.Mzk1QuotientDecompActual
end