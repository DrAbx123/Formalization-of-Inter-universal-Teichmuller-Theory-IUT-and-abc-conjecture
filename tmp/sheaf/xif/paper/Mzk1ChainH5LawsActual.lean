import tmp.sheaf.xif.paper.Mzk1H5HullRayLawsActual
import tmp.sheaf.xif.paper.Mzk1H5DetScalingLawsActualV2
import tmp.sheaf.xif.paper.Mzk1HeightVolumeComparisonActual
import tmp.sheaf.xif.paper.Mzk1H5HullBoundActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1ChainH5LawsActual — chained H5 hull/det/height-volume laws bundle

Chains EXIT0 H5 assets: hull-ray closure, log-det scaling, height-volume comparison
and hull scaling closure.  Interfaces/laws only; no closure; gate NOT PASSED.
Registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ChainH5LawsActual

open LeanFormal.IUT.XiFPaper.Hull06DetTensorActual
open LeanFormal.IUT.XiFPaper.Mzk1H5HullRayLawsActual
open LeanFormal.IUT.XiFPaper.Mzk1H5DetScalingLawsActual
open LeanFormal.IUT.XiFPaper.Mzk1HeightVolumeComparisonActual
open LeanFormal.IUT.XiFPaper.Mzk1H5HullBoundActual
open LeanFormal.IUT.XiFPaper.Hull09H5GapsActual

structure H5ChainLawsBundle where
  hullScale : ∀ {C : Type*} (d : H5HullBound C) (a : ℚ) {x : C},
    x ∈ d.hull → d.scale a x ∈ d.hull
  hvBound : ∀ {X : Type*} (d : HeightVolumeComparison X) (x : X),
    d.height x ≤ d.volume x
  detScaling : ∀ {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ}, A.PosDef → ∀ {c d : ℝ}, 0 < c → 0 < d →
      hull06MatrixLogDet ((c * d) • A) =
        (Fintype.card n : ℝ) * Real.log c + (Fintype.card n : ℝ) * Real.log d +
          hull06MatrixLogDet A

def h5ChainLawsBundle : H5ChainLawsBundle :=
{ hullScale := fun d a hx => d.scale_mem a hx
  hvBound := fun d x => d.height_le_volume x
  detScaling := fun hA hc hd => hull06_det_scaling_compose hA hc hd }

theorem h5Chain_scaling {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    hull06MatrixLogDet ((c * d) • A) =
      (Fintype.card n : ℝ) * Real.log c + (Fintype.card n : ℝ) * Real.log d +
        hull06MatrixLogDet A :=
  h5ChainLawsBundle.detScaling hA hc hd

def chainH5Rows : List (String × String × String) :=
  [ ("bundle", "H5ChainLawsBundle", "DEF (chains EXIT0 H5 laws)"),
    ("det scaling", "h5Chain_scaling", "PROVED (projection)"),
    ("scope", "laws/interfaces only; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem chainH5Rows_length : chainH5Rows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ChainH5LawsActual

end
