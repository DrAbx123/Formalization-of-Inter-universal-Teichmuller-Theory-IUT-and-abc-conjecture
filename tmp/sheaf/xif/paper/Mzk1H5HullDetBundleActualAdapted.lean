import tmp.sheaf.xif.paper.Mzk1H5HullRayLawsActual
import tmp.sheaf.xif.paper.Hull09H5GapsActual
import tmp.sheaf.xif.paper.Mzk1H5DetScalingLawsActualV2

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1H5HullDetBundleActualAdapted (adapted copy, A475 reuse) — H5 hull-ray and determinant-scaling bundle

Reuses the existing H5 hull-ray laws and determinant-scaling laws to expose one
bundle with projections.  No new math; no closure; gate NOT PASSED.
Registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1H5HullDetBundleActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1H5HullRayLawsActual
open LeanFormal.IUT.XiFPaper.Hull09H5GapsActual
open LeanFormal.IUT.XiFPaper.Hull06DetTensorActual
open LeanFormal.IUT.XiFPaper.Mzk1H5DetScalingLawsActual

/-- Bundle of H5 hull-ray closure and log-det scaling laws. -/
structure H5HullDetBundle : Prop where
  ray_downward : ∀ {theta lambda1 lambda2 : ℝ}, lambda1 ≤ lambda2 →
    lambda2 ∈ hullLogVolumeRay theta → lambda1 ∈ hullLogVolumeRay theta
  ray_self : ∀ theta : ℝ, theta ∈ hullLogVolumeRay theta
  scaling_compose : ∀ {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ}, A.PosDef → ∀ {c d : ℝ}, 0 < c → 0 < d →
      hull06MatrixLogDet ((c * d) • A) =
        (Fintype.card n : ℝ) * Real.log c + (Fintype.card n : ℝ) * Real.log d +
          hull06MatrixLogDet A
  scaling_posDef : ∀ {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ}, A.PosDef → ∀ {c : ℝ}, 0 < c → (c • A).PosDef

/-- The existing H5 laws give the bundle. -/
def h5HullDetBundle : H5HullDetBundle :=
{ ray_downward := fun h hmem => hull09_ray_downward h hmem
  ray_self := fun theta => hull09_ray_self theta
  scaling_compose := fun hA hc hd => hull06_det_scaling_compose hA hc hd
  scaling_posDef := fun hA hc => hull06_det_scaling_posDef hA hc }

theorem h5Bundle_ray_downward {theta lambda1 lambda2 : ℝ} (h : lambda1 ≤ lambda2)
    (hmem : lambda2 ∈ hullLogVolumeRay theta) :
    lambda1 ∈ hullLogVolumeRay theta :=
  h5HullDetBundle.ray_downward h hmem

theorem h5Bundle_scaling_compose {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    hull06MatrixLogDet ((c * d) • A) =
      (Fintype.card n : ℝ) * Real.log c + (Fintype.card n : ℝ) * Real.log d +
        hull06MatrixLogDet A :=
  h5HullDetBundle.scaling_compose hA hc hd

def h5HullDetRows : List (String × String × String) :=
  [ ("bundle", "H5HullDetBundle", "DEF (reuses H5 laws)"),
    ("ray projection", "h5Bundle_ray_downward", "PROVED"),
    ("det scaling projection", "h5Bundle_scaling_compose", "PROVED"),
    ("scope", "no new math; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem h5HullDetRows_length : h5HullDetRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1H5HullDetBundleActualAdapted

end
