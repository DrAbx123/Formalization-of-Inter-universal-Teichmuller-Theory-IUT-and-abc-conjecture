/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A845/A850: D_exact, T(l), L6 forward direction, L7 congr form -/

/- D_exact = sum_w weight_w * h_w * log p_w + arch (finite + archimedean).
T(l) = 6*l*(l+5)/((l+4)*(l-3)). With c(l) = (l+4)(l-3)/(24l): T(l) = (l+5)/(4c(l))
(the algebraic identity is taken as the explicit hypothesis hT in l6_forward; it is not
re-proved here to keep this file dependency-free).

L6 FORWARD: c*logQ <= V and V <= ((l+5)/4)*D_exact give logQ <= T(l)*D_exact (proved).
L6 CONVERSE needs V = ((l+5)/4)*D_exact, not claimed.
L7: recorded as congr-invariance form; the actual factorization of D_exact through
rho-bar (with l not dividing ord_p(q)) is the open part. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1RouteCLocalEquivActual

def DExact {ι : Type*} [Fintype ι] (weight h logp : ι → ℝ) (arch : ℝ) : ℝ :=
  (∑ i, weight i * h i * logp i) + arch

def cForm (l : ℝ) : ℝ := (l + 1) / 24 - 1 / (2 * l)

def T (l : ℝ) : ℝ := 6 * l * (l + 5) / ((l + 4) * (l - 3))

theorem cForm_eq (l : ℝ) (hl : l ≠ 0) :
    cForm l = (l + 4) * (l - 3) / (24 * l) := by
  unfold cForm
  field_simp [hl]
  try ring

theorem l6_forward {l c logQ V Dexact : ℝ} (hc : 0 < c)
    (hT : T l = (l + 5) / (4 * c))
    (hSS : c * logQ ≤ V) (hbox : V ≤ ((l + 5) / 4) * Dexact) :
    logQ ≤ T l * Dexact := by
  have hchain : c * logQ ≤ ((l + 5) / 4) * Dexact := le_trans hSS hbox
  have hc4 : 0 < 4 * c := by linarith
  rw [hT, div_mul_eq_mul_div]
  rw [le_div_iff₀ hc4]
  nlinarith

def L7CongrInvariance {ρ : Type*} (Φ : ρ → ℝ) : Prop :=
  ∀ r1 r2 : ρ, r1 = r2 → Φ r1 = Φ r2

theorem l7_congr {ρ : Type*} (Φ : ρ → ℝ) : L7CongrInvariance Φ := by
  intro r1 r2 h
  rw [h]

def routeCLocalRows : List (String × String × String) :=
  [ ("D_exact", "sum weight*h*log p + arch", "DEF") ,
    ("c(l)", "(l+1)/24-1/(2l) = (l+4)(l-3)/(24l)", "PROVED cForm_eq") ,
    ("T(l)", "6l(l+5)/((l+4)(l-3)) = (l+5)/(4c)", "hypothesis hT in l6_forward") ,
    ("L6 forward", "c*logQ<=V, V<=(l+5)/4*D_exact => logQ<=T(l)*D_exact", "PROVED") ,
    ("L6 converse", "needs V = (l+5)/4*D_exact", "NOT CLAIMED") ,
    ("L7", "D_exact factors through rho-bar; l does not divide ord_p(q)", "FORM ONLY (l7_congr)") ]

theorem routeCLocalRows_length : routeCLocalRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1RouteCLocalEquivActual
