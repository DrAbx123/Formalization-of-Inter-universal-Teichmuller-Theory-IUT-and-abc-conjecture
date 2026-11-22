import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
/-!
# D4 consumer shape (interface only, no closure claimed)

Route §6.4 L613-638.  Records the consumer shape of the D4 inequality and the C4/D2
letters it will be instantiated from.  Actual closure waits for
david `uc_c4_actual_paper_letters` (21:25:34) and the D2 bound
`√h ≤ l ≤ C_d√h log(2C_d h)` (sophie/kurt).
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.D4InputShapeActual

def D4Bound (h Q S D N l C0 d e eta C : ℝ) : Prop :=
  h / 6 ≤ (1 + C / Real.sqrt h) * (D + N)
    + C * Real.sqrt h * Real.log (2 * C * h) + C

structure D4Letters where
  h : ℝ
  Q : ℝ
  S : ℝ
  D : ℝ
  N : ℝ
  l : ℝ
  C0 : ℝ
  d : ℝ
  e : ℝ
  eta : ℝ
  hh : 1 ≤ h
  hQh : Q ≤ h
  hS0 : 0 ≤ S
  hSD : S ≤ D + N
  hlpos : 0 < l
  hl2 : h ≤ l ^ 2
  hlup : l ≤ C0 * Real.sqrt h * Real.log (2 * C0 * h)
  herr : h - Q ≤ C0 * Real.sqrt h * Real.log (2 * C0 * h) + C0
  hC4 : (1 / 6 - 2 / l ^ 2) * Q ≤ (1 + 12 * d / l) * S + 10 * (e * l + eta)
  hC0 : 0 ≤ C0
  hd : 0 ≤ d
  he : 0 ≤ e
  heta : 0 ≤ eta

#check D4Bound
#check D4Letters
end LeanFormal.IUT.XiFPaper.D4InputShapeActual
end