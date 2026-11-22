/- U-C D2 (route 6.2, L577-590): the second display of D2 as an actual statement shape.

paper: h := Q_all = normalized degree of ALL finite q-places; Q := the selected
places entering the current initial Theta-data; D2 states (route L583-590)
  sqrt h <= l <= C_d sqrt h log(2 C_d h)
  0 <= h - Q <= C_d sqrt h log(2 C_d h) + C_{K_V}.
The actual h/Q objects are `Mzk1ULQPilotMagnitudeV2Actual.qPilotMagnitudePaper_v2`
(canonical) and the old single-lift `qPilotMagnitudePaper` (LEGACY); the present
file only fixes the STATEMENT SHAPE (D2SecondForm) and its input list, as required
by the L-H package.  No paper inequality is asserted here: the inputs are the
actual objects/estimates to be proved (Legendre/D1 side), listed in the docstrings.
-/
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULD2SecondFormActual

/-- The D2 second-display input package: h = Q_all, Q = selected q magnitude,
the degree constant C_d and the field constant C_{K_V}, with the two D2 facts.
All fields are the actual objects to be instantiated (not new assumptions of
the route: h/Q are the q-heights, the constants are the D1/D2 constants). -/
structure D2SecondForm where
  /-- h = Q_all: normalized degree over all finite q-places. -/
  h : ℝ
  /-- Q: q magnitude of the selected places entering the initial Theta-data. -/
  Q : ℝ
  /-- C_d: the fixed degree-function constant. -/
  Cd : ℝ
  /-- C_{K_V}: the field-dependend constant. -/
  CKV : ℝ
  h_nonneg : 0 ≤ h
  Cd_nonneg : 0 ≤ Cd
  /-- 0 <= h - Q (the first D2 inequality; Q <= h). -/
  h_sub_Q_nonneg : 0 ≤ h - Q
  /-- h - Q <= C_d sqrt(h) log(2 C_d h) + C_{K_V} (the second D2 inequality). -/
  h_sub_Q_le : h - Q ≤ Cd * Real.sqrt h * Real.log (2 * Cd * h) + CKV

/-- PROVED: Q <= h, the first D2 inequality. -/
theorem D2SecondForm.Q_le_h (D : D2SecondForm) : D.Q ≤ D.h :=
  sub_nonneg.mp D.h_sub_Q_nonneg

/-- PROVED: the second D2 display in its conjunction form. -/
theorem D2SecondForm.second_form (D : D2SecondForm) :
    0 ≤ D.h - D.Q ∧ D.h - D.Q ≤ D.Cd * Real.sqrt D.h * Real.log (2 * D.Cd * D.h) + D.CKV :=
  ⟨D.h_sub_Q_nonneg, D.h_sub_Q_le⟩

/-- PROVED: the D2 second display with the first inequality as Q<=h. -/
theorem D2SecondForm.second_form' (D : D2SecondForm) :
    D.Q ≤ D.h ∧ D.h - D.Q ≤ D.Cd * Real.sqrt D.h * Real.log (2 * D.Cd * D.h) + D.CKV :=
  ⟨D.Q_le_h, D.h_sub_Q_le⟩

end LeanFormal.IUT.XiFPaper.Mzk1ULD2SecondFormActual
end
