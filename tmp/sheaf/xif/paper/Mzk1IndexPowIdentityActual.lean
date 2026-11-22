/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1CeilDecompActual
import Mathlib.Tactic
/-! # Index power identity for the corrected torsion decomposition -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IndexPowIdentityActual
/-- Power identity: with `q = p^f` and `f*A - m = f*(A-k) + r`,
the p-power and ceil/remainder forms agree. -/
theorem index_pow_identity
    {p q f A m k r T0 : Nat} (hq : q = p ^ f)
    (hExp : f * A - m = f * (A - k) + r) :
    p ^ (f * A - m) * ((q - 1) / T0) =
      q ^ (A - k) * (p ^ r * ((q - 1) / T0)) := by
  calc
    p ^ (f * A - m) * ((q - 1) / T0)
        = p ^ (f * (A - k) + r) * ((q - 1) / T0) := by rw [hExp]
    _ = (p ^ (f * (A - k)) * p ^ r) * ((q - 1) / T0) := by rw [pow_add]
    _ = p ^ (f * (A - k)) * (p ^ r * ((q - 1) / T0)) := by rw [mul_assoc]
    _ = q ^ (A - k) * (p ^ r * ((q - 1) / T0)) := by rw [hq, ← pow_mul]
end LeanFormal.IUT.XiFPaper.Mzk1IndexPowIdentityActual
end