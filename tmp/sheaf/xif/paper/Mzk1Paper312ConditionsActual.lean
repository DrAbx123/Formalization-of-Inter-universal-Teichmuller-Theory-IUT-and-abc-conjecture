/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Paper312FinalBoundActual
import Mathlib.Tactic

/-! # A785: instantiating the three conditions of Mzk1Paper312FinalBoundActual -/

/- Condition (1) `index_v = residueCard_v^{a_v}`: green theorem
`logShellIntegerIndex_eq_residueCard_pow_of_powerCardHypothesis`
(IntegralLogShellIndexResidueFormula:118) CONSUMES the named input
`LogShellResiduePowerCardHypothesis a`; that input is NOT instantiated for the C3
completion data in the repo (no `PowerCardHypothesis` occurrence outside its own file),
so it is recorded here as the explicit predicate `ResiduePowerCondition`.

Condition (3) `ord_v(q_v) = 1`: `qVFamTensorCoefficient T b = ((qVFamily T b).order : Real)`
(QVFamTensorCoefficientActual:75-86, green); `qVFamily` is the clause-B Tate comparison
parameter (QPilotZeroLocusDivisorActual:55).  The theorem `order = 1` (Tate parameter is a
uniformizer at multiplicative bad places) is NOT in the repo; it is the explicit predicate
`QOrderOne`.

Condition (4) `1 <= a*(Fdeg*(2l))`: purely elementary and PROVED below from a>=1, Fdeg>=1,
2l>=1. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Paper312ConditionsActual

/-- Condition (4): `1 <= a*(Fdeg*(2l))` from the elementary lower bounds. -/
theorem condition4 {a Fdeg l : ℝ} (ha : 1 ≤ a) (hF : 1 ≤ Fdeg) (hl : 1 ≤ 2 * l) :
    (1 : ℝ) ≤ a * (Fdeg * (2 * l)) := by
  have hF2 : (1 : ℝ) ≤ Fdeg * (2 * l) := by nlinarith
  nlinarith

/-- Condition (1) as a predicate: the log-shell integer index is a power of the residue
cardinal. -/
def ResiduePowerCondition (index residueCard a : ℕ) : Prop :=
  index = residueCard ^ a

/-- Under condition (1), the log index is `a * log(residueCard)`. -/
theorem log_index_of_residuePower {index residueCard a : ℕ}
    (h : ResiduePowerCondition index residueCard a) (hq : 0 < (residueCard : ℝ)) :
    Real.log (index : ℝ) = (a : ℝ) * Real.log (residueCard : ℝ) := by
  unfold ResiduePowerCondition at h
  rw [h]
  push_cast
  rw [Real.log_pow]

/-- Condition (3) as a predicate: the q-parameter order is one. -/
def QOrderOne (order : ℕ) : Prop := order = 1

/-- Condition (3) implies the q-order coefficient equals one. -/
theorem coeff_one_of_order_one {order : ℕ} (h : QOrderOne order) :
    ((order : ℝ) = 1) := by
  unfold QOrderOne at h
  rw [h]
  norm_num

/-- **Combined local bound from conditions (1),(3),(4)**: at a bad multiplicative place
with the residue-power condition giving `log index = a*f*log p`, order one giving
`qlog = (f/Fdeg)*log p`, and condition (4), the per-place bound of
`Mzk1Paper312FinalBoundActual` holds (reused, not reproved). -/
theorem local_bound_with_conditions {p f Fdeg l a : ℝ}
    (hp : 0 < p) (hp1 : 1 < p) (hf : 0 < f) (hl : 0 < l) (hF : 0 < Fdeg)
    (ha : 1 ≤ a * (Fdeg * (2 * l))) :
    (f / Fdeg) * Real.log p / (2 * l) ≤ a * f * Real.log p :=
  LeanFormal.IUT.XiFPaper.Mzk1Paper312FinalBoundActual.local_bound_ord_one
    hp hp1 hf hl hF ha

end LeanFormal.IUT.XiFPaper.Mzk1Paper312ConditionsActual
