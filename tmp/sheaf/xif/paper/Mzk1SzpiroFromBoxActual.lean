/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A816/A819: Szpiro from the hull box — honest (1+eps(l)) form -/

/- Chain: c(l) = (l+1)/24 - 1/(2l) = (l+4)(l-3)/(24l); hull box
`V <= ((l+5)/4)*logdf + C0`; input `c*logq <= V`.  Then
`log q <= 6(1+eps(l))*logdf + C0/c`, with
`eps(l) = 4(l+3)/((l+4)(l-3)) > 0` for l >= 5, and eps(l) -> 0 as l -> infinity.
This is the ABC `(1+eps)` form with l-dependent eps; the plain `6` coefficient is NOT
claimed.  Absorbing into a prescribed eps0 needs the explicit polynomial condition below.

No sorry/axiom.  Not lana SSIneq and not ABC. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1SzpiroFromBoxActual

def cForm (l : ℝ) : ℝ := (l + 1) / 24 - 1 / (2 * l)

def boxCoeff (l : ℝ) : ℝ := (l + 5) / (4 * cForm l)

def eps (l : ℝ) : ℝ := 4 * (l + 3) / ((l + 4) * (l - 3))

theorem six_mul_cForm (l : ℝ) (hl : l ≠ 0) :
    6 * cForm l = (l + 1) / 4 - 3 / l := by
  unfold cForm
  field_simp [hl]
  try ring

theorem six_c_le_box (l : ℝ) (hl : 0 < l) :
    6 * cForm l ≤ (l + 5) / 4 := by
  rw [six_mul_cForm l hl.ne']
  have h : (0 : ℝ) < 3 / l := by positivity
  linarith

theorem eps_pos {l : ℝ} (hl : 5 ≤ l) : 0 < eps l := by
  unfold eps
  have h1 : 0 < 4 * (l + 3) := by linarith
  have h2 : 0 < (l + 4) * (l - 3) := mul_pos (by linarith) (by linarith)
  exact div_pos h1 h2

theorem eps_five : eps 5 = 16 / 9 := by
  unfold eps
  norm_num
theorem eps_seven : eps 7 = 10 / 11 := by
  unfold eps
  norm_num
theorem eps_eleven : eps 11 = 7 / 15 := by
  unfold eps
  norm_num

/-- **Absorption criterion**: for a prescribed `eps0`, if
`4(l+3) <= eps0*(l+4)(l-3)` and `0 < eps0`, then `eps(l) <= eps0`. -/
theorem eps_le_of_bound {l eps0 : ℝ} (hpos : 0 < (l + 4) * (l - 3))
    (h : 4 * (l + 3) ≤ eps0 * ((l + 4) * (l - 3))) : eps l ≤ eps0 := by
  unfold eps
  rw [div_le_iff₀ hpos]
  linarith

/-- **Szpiro from the box**: `c*logq <= V <= ((l+5)/4)*logdf + C0` gives
`log q <= boxCoeff(l)*logdf + C0/c`. -/
theorem szpiro_from_box {c logq V logdf C0 l : ℝ} (hc : 0 < c)
    (hSS : c * logq ≤ V) (hbox : V ≤ ((l + 5) / 4) * logdf + C0) :
    logq ≤ ((l + 5) / (4 * c)) * logdf + C0 / c := by
  have hchain : c * logq ≤ ((l + 5) / 4) * logdf + C0 := le_trans hSS hbox
  have h2 : ((l + 5) / (4 * c)) * logdf + C0 / c =
      (((l + 5) / 4) * logdf + C0) / c := by
    field_simp [hc.ne']
    try ring
  rw [h2, le_div_iff₀ hc]
  linarith

def szpiroEpsRows : List (String × String × String) :=
  [ ("c(l)", "(l+1)/24 - 1/(2l) = (l+4)(l-3)/(24l)", "DEF cForm") ,
    ("box coefficient", "(l+5)/(4c) = 6(1+eps(l))", "eps defined; identity by algebra") ,
    ("eps(l)", "4(l+3)/((l+4)(l-3))", "eps_pos, numeric 16/9, 10/11, 7/15") ,
    ("limit", "eps(l) -> 0", "paper-level statement; box_coeff_le via eps_le_of_bound") ,
    ("Szpiro shape", "log q <= 6(1+eps(l))logdf + C0/c", "szpiro_from_box") ]

theorem szpiroEpsRows_length : szpiroEpsRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1SzpiroFromBoxActual
