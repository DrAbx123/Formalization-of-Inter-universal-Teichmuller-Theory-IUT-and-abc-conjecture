import Mathlib.Data.Real.Basic
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false

namespace LeanFormal.IUT.N8Closure.C9P6ArchFactor

/-- Correct arch-corrected target: if hcan = d*hC - (d-1)*hInf,
Qcan = d*Qnorm, and Cor3.12 gives Qcan <= hcan, then
Qcan/d + ((d-1)/d)*hInf <= hC. -/
theorem arch_corrected_target
    {d hC hInf hCan Qcan Qnorm : Real}
    (hd : 0 < d)
    (hCan_eq : hCan = d * hC - (d - 1) * hInf)
    (Qcan_eq : Qcan = d * Qnorm)
    (hcor : Qcan <= hCan) :
    Qcan / d + ((d - 1) / d) * hInf <= hC := by
  have h1 : Qcan + (d - 1) * hInf <= d * hC := by
    nlinarith [hcor, hCan_eq, Qcan_eq]
  have hdne : d ≠ 0 := ne_of_gt hd
  field_simp [hdne]
  nlinarith

/-- If the archimedean readout is nonnegative, Cor3.12 implies P6_norm. -/
theorem p6_norm_of_arch_nonneg
    {d hC hInf hCan Qcan Qnorm : Real}
    (hd : 0 < d)
    (hCan_eq : hCan = d * hC - (d - 1) * hInf)
    (Qcan_eq : Qcan = d * Qnorm)
    (hcor : Qcan <= hCan)
    (hInf_nonneg : 0 <= hInf) :
    Qnorm <= hC := by
  have hcorrect := arch_corrected_target hd hCan_eq Qcan_eq hcor
  have hnonneg : 0 <= ((d - 1) / d) * hInf := by
    have hd1 : 0 <= d - 1 := by linarith
    have hquot : 0 <= (d - 1) / d := div_nonneg hd1 (le_of_lt hd)
    exact mul_nonneg hquot hInf_nonneg
  nlinarith

/-- Exact normalized P6 is the arch-corrected target, not Qcan/d <= hC. -/
theorem p6_norm_exact
    {d hC hInf hCan Qcan Qnorm : Real}
    (hd : 0 < d)
    (hCan_eq : hCan = d * hC - (d - 1) * hInf)
    (Qcan_eq : Qcan = d * Qnorm)
    (hcor : Qcan <= hCan) :
    Qnorm <= hC - ((d - 1) / d) * hInf := by
  have hcorrect := arch_corrected_target hd hCan_eq Qcan_eq hcor
  linarith

end LeanFormal.IUT.N8Closure.C9P6ArchFactor

end