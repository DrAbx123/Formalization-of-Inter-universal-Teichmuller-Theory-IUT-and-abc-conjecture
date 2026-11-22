/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1StepVReductionActual
import tmp.sheaf.xif.paper.Mzk1DExactLowerActual
import tmp.sheaf.xif.paper.Mzk1PrimeConductorRouteActual
import tmp.sheaf.xif.paper.Mzk1ThetaDataLegalityActual
import Mathlib.Tactic

/-! # task-107: P3 target ⇔ explicit inequality (conditional reduction)

See `coord/P3-TARGET-EQUIV.md`.

* `M = V + gap - (sF-1)A = A - R`: pure algebra (PROVED).
* `M ≥ 0 ⇔ e·log p ≤ T(l)·D`: conditional on the explicit dictionary
  `M = c·(T(l)·D - e·log p)` with `c > 0` (hypothesis `hbridge`, GAP-P3-DICT).
* `DExactLowerTarget` (L7) ⇒ `L6ReducedInequality` (L6): green one-way consumer.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1TargetReductionActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepVReductionActual
open LeanFormal.IUT.XiFPaper.Mzk1DExactLowerActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaDataLegalityActual

/-- The explicit target expression `M = V + gap - (sF-1)A`. -/
def MExpr (V gap sF A : Real) : Real := TargetM V gap sF A

/-- The explicit inequality side `e·log p ≤ T(l)·D`. -/
def ExplicitInequality (e logp Tval D : Real) : Prop := e * logp ≤ Tval * D

/-- **Equivalence (conditional on the dictionary `hbridge`)**:
`M ≥ 0 ↔ e·log p ≤ T(l)·D`.  The dictionary `GAP-P3-DICT` is explicit input. -/
theorem targetM_nonneg_iff_explicit
    {V gap sF A e logp Tval D c : Real} (hc : 0 < c)
    (hbridge : MExpr V gap sF A = c * (Tval * D - e * logp)) :
    0 ≤ MExpr V gap sF A ↔ ExplicitInequality e logp Tval D := by
  rw [hbridge]
  unfold ExplicitInequality
  constructor
  · intro h
    have h' : 0 ≤ Tval * D - e * logp := (mul_nonneg_iff_of_pos_left hc).mp h
    linarith
  · intro h
    have h' : 0 ≤ Tval * D - e * logp := by linarith
    exact (mul_nonneg_iff_of_pos_left hc).mpr h'

/-- `M = A - R` under the paper signed-volume relation (pure algebra). -/
theorem M_eq_A_sub_R {V gap sF A R : Real} (hR : R = -(V + gap - sF * A)) :
    MExpr V gap sF A = A - R :=
  targetM_eq_A_sub_R hR

/-- **Conditional target ⇔ L6**: instantiating the dictionary at the abc quantities
(`e = C.e`, `logp = log C.p`, `Tval = T l`, `D = D_exact`). -/
theorem targetM_nonneg_iff_L6
    {V gap sF A e logp Tval D c : Real} (hc : 0 < c)
    (hbridge : MExpr V gap sF A = c * (Tval * D - e * logp))
    (C : PrimeConductorCurve) (l D_exact : ℝ)
    (he : e = (C.e : ℝ)) (hlogp : logp = Real.log (C.p : ℝ))
    (hT : Tval = T l) (hD : D = D_exact) :
    0 ≤ MExpr V gap sF A ↔ L6ReducedInequality C l D_exact := by
  rw [targetM_nonneg_iff_explicit hc hbridge]
  unfold ExplicitInequality L6ReducedInequality
  rw [he, hlogp, hT, hD]

/-- Green one-way consumer: L7 (`DExactLowerTarget`) ⇒ L6, under Mestre–Oesterlé,
Θ-data legality and `0 ≤ log p`. -/
theorem L6_of_DExactLower (hMO : MestreOesterleBound) (C : PrimeConductorCurve)
    (l : ℕ) (L : ThetaDataLegality C l) (D_exact : ℝ)
    (hD : DExactLowerTarget C (l : ℝ) D_exact)
    (hlogp : 0 ≤ Real.log (C.p : ℝ)) :
    L6ReducedInequality C (l : ℝ) D_exact :=
  l6Reduced_of_dExactLower hMO C l L D_exact hD hlogp

/-- Chain rows (honest status). -/
def targetReductionRows : List (String × String × String) :=
  [ ("MExpr", "M = V+gap-(sF-1)A", "DEF"),
    ("M_eq_A_sub_R", "M = A-R under signed-volume R", "PROVED (algebra)"),
    ("targetM_nonneg_iff_explicit", "M>=0 <=> e log p <= T(l) D, conditional on hbridge", "PROVED (conditional)"),
    ("targetM_nonneg_iff_L6", "M>=0 <=> L6ReducedInequality C l D, conditional on hbridge", "PROVED (conditional)"),
    ("hbridge", "M = c*(T(l)*D - e*log p), GAP-P3-DICT explicit input", "GAP (input hypothesis)"),
    ("L6_of_DExactLower", "L7 => L6 (one-way)", "PROVED (green consumer; converse UNKNOWN)") ]

theorem targetReductionRows_length : targetReductionRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1TargetReductionActual

end
