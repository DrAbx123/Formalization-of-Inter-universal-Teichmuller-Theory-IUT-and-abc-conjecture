/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.external.ported.lana_core.Iut.WallEquiv.Gap
import Mathlib.Tactic

/-! # A1109: faithful enlargement E and its bridge to lana gap

| field | value |
|---|---|---|
| Status | **LANA-DEPENDENT / DEFERRED**: requires `tmp.external.ported.lana_core.Iut.WallEquiv.Gap.olean`, currently absent; not in critical path. Original status: DEFINITION + BRIDGE: `faithfulGapHullAt` is the packet sum `Σ_c tupleWeight * ind2Term` (finite places) and 0 at ∞; `faithfulEnlargement` is `(1/nC) Σ_i Σᶠ_vQ faithfulGapHullAt`; `faithfulEnlargement_eq_gap` is proved from lana `gap_eq` if the ported `Gap` olean exists. |
| Source | lana `Iut/WallEquiv/Gap.lean:895` (`gapHullAt`), `:916` (`gapHullAt_eq`), `:961` (`gap_eq`) |
| GAP | `tmp.external.ported.lana_core.Iut.WallEquiv.Gap.olean` is not yet built (lana_core currently only 2 oleans); the file is queued for after the lana_core build. |
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1FaithfulEnlargementActual

open LeanFormal.IUT
open LeanFormal.IUT.WallEquiv

variable (D : InitialThetaData.{0})

/-- The faithful local enlargement at a finite place: the packet sum of
`tupleWeight * ind2Term`; at `∞` it is `0`. -/
noncomputable def faithfulGapHullAt (i : Fin (nC D)) :
    RationalPlace → ℝ
  | .finite p =>
      ∑ c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p),
        tupleWeight (.finite p) c * ind2Term D i p c
  | .infinite => 0

/-- The faithful global enlargement `E = (1/nC) Σ_i Σᶠ_vQ faithfulGapHullAt`. -/
noncomputable def faithfulEnlargement : ℝ :=
  (∑ i : Fin (nC D), ∑ᶠ vQ : RationalPlace, faithfulGapHullAt D i vQ) /
    (nC D : ℝ)

/-- The faithful local term is lana's `gapHullAt` (finite case is definitional;
`∞` case is its zero value). -/
theorem faithfulGapHullAt_eq_gapHullAt (i : Fin (nC D)) (vQ : RationalPlace) :
    faithfulGapHullAt D i vQ = gapHullAt D i vQ := by
  rcases vQ with p | _ <;> rfl

/-- **Bridge**: the faithful enlargement is lana's `gap`. -/
theorem faithfulEnlargement_eq_gap : faithfulEnlargement D = gap D := by
  rw [faithfulEnlargement, gap_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact finsum_congr fun vQ => faithfulGapHullAt_eq_gapHullAt D i vQ

def rows : List (String × String × String) :=
  [ ("faithfulGapHullAt", "Σ_c w_c ind2Term; 0 at ∞", "DEF"),
    ("faithfulEnlargement", "(1/nC) Σ_i Σᶠ_vQ faithfulGapHullAt", "DEF"),
    ("faithfulGapHullAt_eq_gapHullAt", "local bridge", "PROVED (rfl)"),
    ("faithfulEnlargement_eq_gap", "E = lana gap", "PROVED from gap_eq (after lana_core)") ]

theorem rows_length : rows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1FaithfulEnlargementActual

end