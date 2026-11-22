import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealGeometryReduction
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction
import tmp.sheaf.xif.paper.Hull06DetTensorActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: O^x-stabilization|sourceScalingUnits|hull closure|O(-)^{-1}|det tensor bookkeeping|hullLogVolumeRay -> hits LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/CardHullRealGeometryReduction.lean:94 sourceScalingUnits_subset_sourceHolomorphicHull, :108 sourceHolomorphicHull_eq_closure, HullDeterminantLogVolumeReduction.lean:483 detTensorPowerBookkeeping_scalarLogDegree, :501 hullLogVolumeRay, :505 mem_hullLogVolumeRay_iff -> REUSE (H5 class-B gaps now: O^x-stabilization REUSED-PROVED; O(-)^{-1} normalization has tree bookkeeping witness; full paper normalization + hull<=image volume remain named).

# [Hull] 09: H5 class-B gaps - O^x-stabilization and O(-)^{-1} normalization rows

Corpus: IUT III Remark 3.9.5(i) (hull = least lambda*O; O^x-stabilization),
Step (xi-d)/(xi-f) (det tensor bookkeeping; hull log-volume ray),
Step (xi) corpus 10750-10987; Cor 3.12 statement corpus 10324-10353; conclusion 10897.
CONTENT (class A reuse, no re-proof):
* O^x-stabilization: the tree PROVES that every source scaling unit lies in the
  source holomorphic hull, and that the hull is exactly the submonoid closure of
  the possible theta-pilot images together with the scaling units.
* O(-)^{-1} normalization: the tree PROVES the det-tensor bookkeeping witness
  (M-fold det tensor power scales the normalized log-volume by M) and the
  hull-log-volume ray membership (Step (xi-f)).
NAMED CLASS-B (not claimed): the full paper O(-)^{-1} normalization on the
arithmetic line bundle, and the hull<=image-volume inequality (tree records it
as not a formal consequence of the value layer: report section 17, R9/R10).
Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Hull09H5GapsActual

universe ua uv upi umon ui

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Hull06DetTensorActual

variable {l : PrimeGeFive} {V : Type uv}

/-- **O^x-stabilization (class A, reused):** every source scaling unit lies in the
source holomorphic hull (Remark 3.9.5(i) at the value layer). -/
theorem hull09_scalingUnits_subset_hull (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceScalingUnits v ⊆ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) :=
  sourceScalingUnits_subset_sourceHolomorphicHull I v R n

/-- **Hull generator characterization (class A, reused):** the hull is exactly the
submonoid closure of the possible theta-pilot images and the scaling units. -/
theorem hull09_hull_eq_closure (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceHolomorphicHull v R n =
      Submonoid.closure (I.possibleThetaPilotImageSet v R n ∪ I.sourceScalingUnits v) :=
  sourceHolomorphicHull_eq_closure I v R n

/-- **O(-)^{-1} / det tensor bookkeeping (class A, reused):** the M-fold det tensor
power bookkeeping with normalized log-volume scaled by M. -/
noncomputable def hull09DetTensorBookkeeping (M : Nat) (hM : 0 < M) :
    DetTensorPowerLogVolumeBookkeeping ℝ :=
  detTensorPowerBookkeeping_scalarLogDegree M hM

/-- The bookkeeping's tensor-power exponent is M (definitional). -/
theorem hull09DetTensorBookkeeping_exponent (M : Nat) (hM : 0 < M) :
    (hull09DetTensorBookkeeping M hM).tensorPowerExponent = M := rfl

/-- **Step (xi-f) ray (class A, reused):** the paper's R_{<= -|log(Theta)|} ray is
the ray of the hull log-volume. -/
theorem hull09_ray_mem_iff {thetaHullLogVolume lambdaValue : ℝ} :
    lambdaValue ∈ hullLogVolumeRay thetaHullLogVolume ↔
      lambdaValue ≤ thetaHullLogVolume :=
  mem_hullLogVolumeRay_iff

/-- H5 class-B gap rows after this file (status ledger). -/
def hull09Rows : List (String × String × String) :=
  [ ("O^x-stabilization of the hull", "A", "REUSED-PROVED CardHullRealGeometryReduction:94 sourceScalingUnits_subset_sourceHolomorphicHull")
  , ("hull = submonoid closure(images, scalings)", "A", "REUSED-PROVED CardHullRealGeometryReduction:108 sourceHolomorphicHull_eq_closure")
  , ("det tensor bookkeeping (M-fold log-volume scaling)", "A", "REUSED-PROVED HullDeterminantLogVolumeReduction:483 detTensorPowerBookkeeping_scalarLogDegree")
  , ("Step (xi-f) hull log-volume ray", "A", "REUSED-PROVED HullDeterminantLogVolumeReduction:501/:505")
  , ("full paper O(-)^{-1} normalization on the arithmetic line bundle", "B", "NAMED; only the bookkeeping witness is formalized")
  , ("hull <= image-volume inequality", "B", "NAMED; tree doc records it as not a formal consequence of the value layer (report section 17 R9/R10)") ]

/-- The H5 gap row record has six rows. -/
theorem hull09Rows_length : hull09Rows.length = 6 := rfl

#check hull09_scalingUnits_subset_hull
#check hull09_hull_eq_closure
#check hull09DetTensorBookkeeping
#check hull09_ray_mem_iff
#check hull09Rows_length

end LeanFormal.IUT.XiFPaper.Hull09H5GapsActual
end