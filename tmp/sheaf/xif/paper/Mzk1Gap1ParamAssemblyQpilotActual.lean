/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Mzk1Gap1ParamAssemblyQpilotActual — parameterized Gap1 assembly (A673)

Parameterized (region-volume-agnostic) assembly of the Gap-1 equivalence: for any
positive region volume `vol`, the multiplicative comparison, the ratio form and the
log form are equivalent.  Instantiated at arbitrary positive volumes, this covers
the corrected region (inverse-product) and the canonical region alike. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Gap1ParamAssemblyQpilotActual

/-- Parameterized Gap-1: multiplicative ↔ log form for any positive volume. -/
theorem gap1_param_iff_log {h vol epsilon : Real} (hvol : 0 < vol) (hh : 0 < h)
    (heps : 0 < 1 + epsilon) :
    (h ≤ (1 + epsilon) * vol) ↔ (Real.log h ≤ Real.log (1 + epsilon) + Real.log vol) := by
  have hprod : 0 < (1 + epsilon) * vol := mul_pos heps hvol
  constructor
  · intro h1
    have hlog := Real.log_le_log hh h1
    rw [Real.log_mul (ne_of_gt heps) (ne_of_gt hvol)] at hlog
    exact hlog
  · intro hlog
    have : Real.log h ≤ Real.log ((1 + epsilon) * vol) := by
      rw [Real.log_mul (ne_of_gt heps) (ne_of_gt hvol)]
      exact hlog
    exact (Real.log_le_log_iff hh hprod).mp this

/-- Parameterized Gap-1: multiplicative → ratio form. -/
theorem gap1_param_ratio {h vol epsilon : Real} (hvol : 0 < vol)
    (h1 : h ≤ (1 + epsilon) * vol) : h / vol ≤ 1 + epsilon :=
  (div_le_iff₀ hvol).mpr h1

/-- Parameterized three-form equivalence. -/
theorem gap1_param_three {h vol epsilon : Real} (hvol : 0 < vol) (hh : 0 < h)
    (heps : 0 < 1 + epsilon) :
    (h ≤ (1 + epsilon) * vol) ↔
      ((h / vol ≤ 1 + epsilon) ∧
        (Real.log h ≤ Real.log (1 + epsilon) + Real.log vol)) :=
  ⟨fun h1 => ⟨gap1_param_ratio hvol h1, (gap1_param_iff_log hvol hh heps).mp h1⟩,
   fun ⟨_, hlog⟩ => (gap1_param_iff_log hvol hh heps).mpr hlog⟩

/-- Parameterized Gap-1, log input: log inequality gives the comparison. -/
theorem gap1_param_of_log {h vol epsilon : Real} (hvol : 0 < vol) (hh : 0 < h)
    (heps : 0 < 1 + epsilon)
    (hlog : Real.log h ≤ Real.log (1 + epsilon) + Real.log vol) :
    h ≤ (1 + epsilon) * vol :=
  (gap1_param_iff_log hvol hh heps).mpr hlog

/-- Rows for the parameterized assembly. -/
def gap1ParamRows : List (String × String) :=
  [ ("multiplicative ↔ log", "PROVED"),
    ("multiplicative → ratio", "PROVED"),
    ("three-form equivalence", "PROVED"),
    ("log → multiplicative", "PROVED") ]

theorem gap1ParamRows_length : gap1ParamRows.length = 4 := rfl

#check gap1_param_iff_log
#check gap1_param_three
#check gap1_param_of_log
#check gap1ParamRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Gap1ParamAssemblyQpilotActual
end
