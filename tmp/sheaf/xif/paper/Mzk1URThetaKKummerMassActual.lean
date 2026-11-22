/- J1-M Kummer mass (kurt): layered interface.

Layer 1 (later, uses Mathlib donor LinearMap.exists_map_addHaar_eq_smul_addHaar).
Layer 2 (EXPLICIT OBLIGATION, not terminal): HaarScaleData records the Haar scaling factor c>0
with mu.map L = c • mu. Its concrete value must be discharged (1-2 batches) by the DVR index +
Haar subgroup index route; it must NOT appear in the final P8-P dependency list.
Layer 3 (proved here, pure algebra): if q = a^(2l) then (1/(2l))*log q = log a, which is the
local Kummer mass identity once the Haar index gives (1/[L:Q_p])log(mu(aO)/mu(O)) = log a.

Default heartbeats.
-/
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators NNReal Padic

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKKummerMassActual

variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
variable [FiniteDimensional ℚ_[p] E] [ProperSpace E] [MeasurableSpace E] [BorelSpace E]

/-- J1-M input obligation (Layer 2): the Haar scaling factor of a ℚ_p-linear self-map, with its
defining property. Explicit obligation: to be discharged by dvr_index/haar_subgroup_index; not a
terminal assumption. -/
structure HaarScaleData (μ : MeasureTheory.Measure E) (L : E →L[ℚ_[p]] E) where
  /-- the scaling factor -/
  c : ℝ≥0
  /-- the factor is positive -/
  c_pos : 0 < c
  /-- pushforward scaling property -/
  c_spec : μ.map L = c • μ

/-- Layer 3: with q = a^(2l), the normalized log mass equals log a. -/
theorem log_div_two_l (a : ℝ) (ha : 0 < a) (l : ℕ) (hl : 0 < l) :
    (1 / (2 * (l : ℝ))) * Real.log (a ^ (2 * l)) = Real.log a := by
  rw [Real.log_pow]
  push_cast
  field_simp

/-- Layer 3, mass form: c = a^(2l) gives (1/(2l)) log c = log a. -/
theorem kummer_mass_algebra (a : ℝ) (ha : 0 < a) (l : ℕ) (hl : 0 < l) (q : ℝ)
    (hq : q = a ^ (2 * l)) :
    (1 / (2 * (l : ℝ))) * Real.log q = Real.log a := by
  rw [hq, log_div_two_l a ha l hl]

#print axioms log_div_two_l
#print axioms kummer_mass_algebra

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKKummerMassActual
end