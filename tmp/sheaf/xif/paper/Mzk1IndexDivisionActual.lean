/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1QuotientDecompActual
import tmp.sheaf.xif.paper.Mzk1TorsionSplitActual
import Mathlib.Tactic
/-! # Index division for the corrected torsion decomposition -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IndexDivisionActual
open LeanFormal.IUT.XiFPaper.Mzk1QuotientDecompActual
/-- Index division: cancel the p-part and `T0` from the quotient. -/
theorem index_division
    {p q f A m T0 T : Nat} (hp : 0 < p) (hT0pos : 0 < T0)
    (hq : q = p ^ f) (hT : T = p ^ m * T0)
    (hT0 : T0 ∣ q - 1) (hm : m ≤ f * A) :
    q ^ A * (q - 1) / T = p ^ (f * A - m) * ((q - 1) / T0) :=
  quotient_decomp hp hT0pos hq hT hT0 hm
end LeanFormal.IUT.XiFPaper.Mzk1IndexDivisionActual
end