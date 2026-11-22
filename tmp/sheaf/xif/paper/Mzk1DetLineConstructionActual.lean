/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import Mathlib.Tactic

/-! # Route B #3 step 1-2: actual determinant line of the source and relative determinant

Uses the actual `LineBundle = FractionalIdeal (nonZeroDivisors O_k) k` of
`DeterminantLogVolumeActual` (`LineBundle`, `determinantLine`, `determinantNorm`,
`globalLogVolume`, `localizedLine`).  Constructs the relative determinant
`D(H,O) = det(H) * det(O)^{-1}` (B4.4/B5) and proves its global log-volume is the
difference of the log-volumes (the common-coordinate `log |det B_H| - log |det B_O|`
identity, B5 at the global level).  The per-place and archimedean computations are
separate steps; `localizedLine` is the actual place-level object.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1DetLineConstructionActual

open LeanFormal.IUT.PaperDeterminantLogVolume

variable {k : Type} [Field k] [NumberField k]

/-- The actual relative determinant line `D(H,O) = det(H) * det(O)^{-1}`. -/
def relativeDetLine (H O : LineBundle (k := k)) : LineBundle (k := k) :=
  determinantLine (k := k) H * (determinantLine (k := k) O)⁻¹

theorem relativeDetLine_eq (H O : LineBundle (k := k)) :
    relativeDetLine (k := k) H O =
      determinantLine (k := k) H * (determinantLine (k := k) O)⁻¹ := rfl

/-- The determinant norm of the inverse line bundle. -/
theorem determinantNorm_inv (O : LineBundle (k := k)) (hO : O ≠ 0) :
    determinantNorm (k := k) O⁻¹ = (determinantNorm (k := k) O)⁻¹ := by
  have hprod : O * O⁻¹ = (1 : LineBundle (k := k)) := mul_inv_cancel₀ hO
  have h := congrArg (determinantNorm (k := k)) hprod
  rw [determinantNorm_mul, determinantNorm_one] at h
  exact eq_inv_of_mul_eq_one_right h

/-- The log-volume of the inverse line bundle is the negative log-volume. -/
theorem globalLogVolume_inv (O : LineBundle (k := k)) (hO : O ≠ 0) :
    globalLogVolume (k := k) O⁻¹ = - globalLogVolume (k := k) O := by
  have hOinv : O⁻¹ ≠ 0 := inv_ne_zero hO
  have hnorm := determinantNorm_inv (k := k) O hO
  have hOpos : (0 : Rat) < determinantNorm (k := k) O := by
    exact lt_of_le_of_ne (determinantNorm_nonneg O)
      (Ne.symm (mt (determinantNorm_eq_zero_iff O).mp hO))
  unfold globalLogVolume
  rw [hnorm]
  push_cast
  exact Real.log_inv _

/-- **B4/B5 (global form)**: the relative determinant log-volume is the difference of
the two determinant log-volumes; in common coordinates this is
`log |det B_H| - log |det B_O|`. -/
theorem globalLogVolume_relativeDetLine
    (H O : LineBundle (k := k)) (hH : H ≠ 0) (hO : O ≠ 0) :
    globalLogVolume (k := k) (relativeDetLine (k := k) H O) =
      globalLogVolume (k := k) H - globalLogVolume (k := k) O := by
  have hOinv : O⁻¹ ≠ 0 := inv_ne_zero hO
  rw [relativeDetLine, determinantLine_eq, determinantLine_eq,
    globalLogVolume_mul H O⁻¹ hH hOinv, globalLogVolume_inv O hO]
  ring

/-- The relative determinant log-volume as a function (the source degree dictionary). -/
def relativeDetLog (H O : LineBundle (k := k)) : Real :=
  globalLogVolume (k := k) (relativeDetLine (k := k) H O)

theorem relativeDetLog_eq_ratio
    (H O : LineBundle (k := k)) (hH : H ≠ 0) (hO : O ≠ 0) :
    relativeDetLog (k := k) H O =
      Real.log ((determinantNorm (k := k) H : Real) / (determinantNorm (k := k) O : Real)) := by
  have hOinv : O⁻¹ ≠ 0 := inv_ne_zero hO
  have hHpos : (0 : Rat) < determinantNorm (k := k) H := by
    exact lt_of_le_of_ne (determinantNorm_nonneg H)
      (Ne.symm (mt (determinantNorm_eq_zero_iff H).mp hH))
  have hOpos : (0 : Rat) < determinantNorm (k := k) O := by
    exact lt_of_le_of_ne (determinantNorm_nonneg O)
      (Ne.symm (mt (determinantNorm_eq_zero_iff O).mp hO))
  rw [relativeDetLog, globalLogVolume_relativeDetLine H O hH hO]
  unfold globalLogVolume
  rw [← Real.log_div (ne_of_gt (by exact_mod_cast hHpos : (0:Real) < (determinantNorm (k := k) H : Real)))
    (ne_of_gt (by exact_mod_cast hOpos : (0:Real) < (determinantNorm (k := k) O : Real)))]

def detLineRows : List (String × String × String) :=
  [ ("relativeDetLine", "D(H,O) = det(H) * det(O)^{-1} on the actual fractional-ideal line bundle", "CONSTRUCTED"),
    ("determinantNorm_inv", "det norm of inverse line bundle", "PROVED"),
    ("globalLogVolume_inv", "log of inverse line bundle = -log", "PROVED"),
    ("globalLogVolume_relativeDetLine", "B4/B5 global: log D(H,O) = log H - log O", "PROVED"),
    ("relativeDetLog_eq_ratio", "log |det B_H| - log |det B_O| as a real log-ratio", "PROVED"),
    ("localizedLine", "actual place-level localization of the relative determinant", "EXISTS (DeterminantLogVolumeActual:108)"),
    ("per-place B5", "index computation at each finite place", "NEXT (localizedLine + index)"),
    ("archimedean metric", "infinite-place determinant metric", "NEXT") ]

theorem detLineRows_length : detLineRows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1DetLineConstructionActual

end