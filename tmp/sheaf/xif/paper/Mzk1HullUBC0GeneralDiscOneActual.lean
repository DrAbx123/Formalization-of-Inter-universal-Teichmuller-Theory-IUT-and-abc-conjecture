/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HullUBC0AbsorptionActual
import Mathlib.Tactic
/-! # GAP-P7-HULL-UB general disc=1: exact C0 absorption condition -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1HullUBC0GeneralDiscOneActual
open LeanFormal.IUT LeanFormal.IUT.XiFPaper.Mzk1StepVVolumeUpperActual
variable {l : PrimeGeFive}
theorem paperBox_disc_one_cond_one_zero :
    paperBox (l.value : Real) 0 0 0 = 0 := by
  rw [paperBox_eq]
  ring
theorem not_one_le_paperBox_disc_one_cond_one_zero :
    ¬ 1 ≤ paperBox (l.value : Real) 0 0 0 := by
  rw [paperBox_disc_one_cond_one_zero]
  norm_num
/-- Exact condition for the general disc=1, C0=0 absorption. -/
theorem absorption_condition_disc_one (logf : Real) :
    1 ≤ paperBox (l.value : Real) 0 logf 0 ↔
      4 / ((l.value : Real) + 5) ≤ logf := by
  rw [paperBox_eq]
  have hl : (0 : Real) < (l.value : Real) + 5 := by
    have : (5 : Real) ≤ l.value := by exact_mod_cast l.ge_five
    linarith
  constructor
  · intro h
    have hcoef : 0 < ((l.value : Real) + 5) / 4 := by positivity
    rw [div_le_iff₀ hl]
    nlinarith
  · intro h
    rw [div_le_iff₀ hl] at h
    nlinarith
end LeanFormal.IUT.XiFPaper.Mzk1HullUBC0GeneralDiscOneActual
end
