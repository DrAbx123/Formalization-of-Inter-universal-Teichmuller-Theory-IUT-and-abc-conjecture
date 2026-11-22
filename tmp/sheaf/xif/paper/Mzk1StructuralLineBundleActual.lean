/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.S2735QPilotLineBundleActual
import tmp.sheaf.xif.paper.S2736QPilotLineBundleHweightvol
import Mathlib.Tactic

/-! # A1085: Form C — rank-one line-bundle comparison for xi-d

| field | value |
|---|---|---|
| Status | PARTIAL: the arithmetic conclusion `-A ≤ -R` from the line-bundle comparison is PROVED; the concrete bridge `A = globalLogVolume(qBundle)/(2ℓ)`, `R = globalLogVolume(detBundle)/(2ℓ)`, and the determinant line `detBundle` are explicit GAP fields. |
| Source | `DeterminantLogVolumeActual` (`LineBundle`, `determinantLine`, `determinantNorm`, `globalLogVolume`, `localizedLine`); `S2735QPilotLineBundleActual` (`qPilotLineBundle`); `S2736QPilotLineBundleHweightvol` (`S2736QPilotLineBundleLogVolume`); `S2807_thetaHullVolume_eq_haarRegion` |
| GAP | `qPilotLineBundle` is a fractional ideal, not the theta determinant line; `globalLogVolume qBundle = log(deg q)` is positive, while `−A` is negative; the normalization `/(2ℓ)` and the theta-side determinant line identity are not theorem. |
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1StructuralLineBundleActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual
open LeanFormal.IUT.XiFPaper.S2736QPilotLineBundleHweightvol
open LeanFormal.IUT.PaperDeterminantLogVolume

variable {K : Type} [Field K] [NumberField K]

/-- Form C data: two rank-one line bundles and the normalized log-volume
comparison.  `l` is the prime, `2l` is the normalization denominator. -/
structure FormCLineBundleComparison (l : PrimeGeFive) (K : Type)
    [Field K] [NumberField K] where
  qBundle : LineBundle (k := K)
  detBundle : LineBundle (k := K)
  A : Real
  R : Real
  hA : A = globalLogVolume (k := K) qBundle / (2 * (l.value : Real))
  hR : R = globalLogVolume (k := K) detBundle / (2 * (l.value : Real))
  hcmp : globalLogVolume (k := K) detBundle ≤ globalLogVolume (k := K) qBundle

namespace FormCLineBundleComparison

variable {l : PrimeGeFive} {K : Type} [Field K] [NumberField K]
  (D : FormCLineBundleComparison l K)

/-- **Form C arithmetic conclusion**: if the determinant line has no larger
normalized global log-volume than the q line, then `-A ≤ -R`. -/
theorem neg_A_le_neg_R : -D.A ≤ -D.R := by
  have hl : (0 : Real) < 2 * (l.value : Real) := by
    have hl0 : (0 : Real) < (l.value : Real) := by exact_mod_cast l.prime.pos
    linarith
  have hRle : D.R ≤ D.A := by
    rw [D.hR, D.hA]
    exact div_le_div_of_nonneg_right D.hcmp hl.le
  linarith

end FormCLineBundleComparison

/-! ## Concrete S1487/q-pilot side -/

/-- The field of the concrete Gaussian arithmetic. -/
abbrev QK (l : PrimeGeFive) : Type := (S2735Arithmetic l).K

/-- The concrete q-pilot line bundle, as a `LineBundle`. -/
noncomputable def qPilotLineBundleC (l : PrimeGeFive) :
    LineBundle (k := QK l) :=
  qPilotLineBundle l

/-- q-pilot normalized log-volume bridge (explicit GAP): `A` is the global
log-volume of the q-pilot line bundle divided by `2ℓ`. -/
def QPilotGlobalLogBridge (l : PrimeGeFive) (A : Real) : Prop :=
  A = globalLogVolume (k := QK l) (qPilotLineBundleC l) / (2 * (l.value : Real))

/-- Theta/determinant normalized log-volume bridge (explicit GAP): `R` is the
global log-volume of the determinant line divided by `2ℓ`. -/
def ThetaDetGlobalLogBridge (l : PrimeGeFive) (detBundle : LineBundle (k := QK l))
    (R : Real) : Prop :=
  R = globalLogVolume (k := QK l) detBundle / (2 * (l.value : Real))

/-- Form C concrete target for S1487: a determinant line whose normalized
log-volume is `R` and is ≤ the q-pilot normalized log-volume `A`. -/
def S1487FormCData (l : PrimeGeFive) : Prop :=
  ∃ (detBundle : LineBundle (k := QK l)) (A R : Real),
    QPilotGlobalLogBridge l A ∧
    ThetaDetGlobalLogBridge l detBundle R ∧
    globalLogVolume (k := QK l) detBundle ≤ globalLogVolume (k := QK l) (qPilotLineBundleC l)

/-- Conditional Form C conclusion for the concrete q-pilot side. -/
theorem S1487FormC_variant (l : PrimeGeFive) (h : S1487FormCData l) :
    ∃ A R : Real, -A ≤ -R := by
  obtain ⟨detBundle, A, R, hA, hR, hcmp⟩ := h
  refine ⟨A, R, ?_⟩
  have hl : (0 : Real) < 2 * (l.value : Real) := by
    have hl0 : (0 : Real) < (l.value : Real) := by exact_mod_cast l.prime.pos
    linarith
  have hRle : R ≤ A := by
    rw [hR, hA]
    exact div_le_div_of_nonneg_right hcmp hl.le
  linarith

def rows : List (String × String × String) :=
  [ ("FormCLineBundleComparison", "qBundle/detBundle/A/R + hA/hR/hcmp", "DEF"),
    ("neg_A_le_neg_R", "-A <= -R from line-bundle comparison", "PROVED"),
    ("QPilotGlobalLogBridge", "A = globalLogVolume qBundle/(2l)", "GAP (Prop)"),
    ("ThetaDetGlobalLogBridge", "R = globalLogVolume detBundle/(2l)", "GAP (Prop)"),
    ("S1487FormCData", "concrete existential", "GAP (Prop)"),
    ("S1487FormC_variant", "-A <= -R from S1487FormCData", "PROVED (conditional)") ]

theorem rows_length : rows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1StructuralLineBundleActual

end