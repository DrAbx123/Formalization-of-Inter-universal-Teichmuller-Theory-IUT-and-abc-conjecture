/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PrimeConductorABCActual
import tmp.sheaf.xif.paper.Mzk1PrimeConductorRouteActual
import Mathlib.Tactic

/-! # Mestre–Oesterlé normalized surrogate consumption (class-B explicit input)

**Important**: the Lean Prop `MestreOesterleBound` used here is a *normalized surrogate*
(Szpiro-6 shape `logq ≤ 6 logd + C` and conductor-exponent packaging), NOT the original
Mestre–Oesterlé theorem (Zbl 0693.14004, Thm 1/2: semi-stable curves, `|Δ|` an m-th power
⇒ m ≤ 5 plus rational m-torsion; prime conductor ⇒ Δ = ±p up to listed exceptions).
See `coord/EXTERNAL-CITATIONS-20261114.md` §7 and `coord/MESTERE-USE-DIRECTIVE.md`.
The theorems below only consume the surrogate Prop as an explicit class-B parameter. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1MestreUseWiringActual

open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorABCActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual

/-- ABC form of MO is consumed directly. -/
theorem logq_le_six_logd_add_C (logq logd C : Real)
    (hMO : Mzk1PrimeConductorABCActual.MestreOesterleBound logq logd C) :
    logq ≤ 6 * logd + C :=
  hMO

/-- Route form of MO gives the prime-conductor exponent bound. -/
theorem primeConductor_e_le_five (hMO : Mzk1PrimeConductorRouteActual.MestreOesterleBound)
    (C : PrimeConductorCurve) : C.e ≤ 5 :=
  (hMO C).1

/-- Route form of MO gives the threshold bound for p > 37. -/
theorem primeConductor_e_le_two (hMO : Mzk1PrimeConductorRouteActual.MestreOesterleBound)
    (C : PrimeConductorCurve) (hp : 37 < C.p) : C.e ≤ 2 :=
  (hMO C).2 hp

/-- Non-applicability certificate for the local/generator gaps: the MO route form only
produces conductor exponent bounds, never generator valuations. -/
theorem mestre_route_shape (hMO : Mzk1PrimeConductorRouteActual.MestreOesterleBound) :
    ∀ C : PrimeConductorCurve, C.e ≤ 5 ∧ (37 < C.p → C.e ≤ 2) :=
  hMO

def mestreRows : List (String × String × String) :=
  [ ("logq_le_six_logd_add_C", "ABC surrogate consumed (normalized Szpiro-6 shape)", "PROVED (class-B hMO surrogate)"),
    ("primeConductor_e_le_five", "e <= 5 from route surrogate", "PROVED (class-B hMO)"),
    ("primeConductor_e_le_two", "p>37 => e<=2 (surrogate packaging)", "PROVED (class-B hMO)"),
    ("mestre_route_shape", "route surrogate full shape (not original MO)", "PROVED (class-B hMO)") ]

theorem mestreRows_length : mestreRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1MestreUseWiringActual

end
