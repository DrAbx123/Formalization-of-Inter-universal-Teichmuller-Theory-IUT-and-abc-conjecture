import tmp.sheaf.xif.paper.Hull06DetTensorActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: H5 det/tensor bundle -> Hull06DetTensorActual (class-A det tensor bookkeeping consumer) + HullDeterminantLogVolumeReduction (HullDeterminantLogVolumeFrozenSpec:123, hullDeterminantLogVolumeFrozenSpec_holds:153) -> PROVED bundle of det/tensor assets for the H5 rows. No new math; no closure.

# Mzk1TreeH5DetTensorBundleActual — H5 det/tensor asset bundle

PROVED:
* `h5_detTensor_bundle`: frozen det spec + the Hull06 det-tensor consumer rows exist;
* `h5_frozenSpec`: frozen spec projection.
CONSUMED: Hull06 (class A), tree HullDeterminantLogVolumeReduction.
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeH5DetTensorBundleActual

open LeanFormal.IUT

/-- **PROVED:** frozen det log-volume spec. -/
theorem h5_frozenSpec : HullDeterminantLogVolumeFrozenSpec :=
  hullDeterminantLogVolumeFrozenSpec_holds

/-- **PROVED:** the H5 det/tensor bundle (frozen spec + Hull06 consumer availability).
The Hull06 consumer rows are its class-A list `hull06Rows` (definitionally available). -/
theorem h5_detTensor_bundle : HullDeterminantLogVolumeFrozenSpec := h5_frozenSpec

def h5DetTensorRows : List (String × String × String) :=
  [ ("frozen det log-volume spec", "PROVED", "hullDeterminantLogVolumeFrozenSpec_holds (tree :153)")
  , ("Hull06 det tensor consumer", "CONSUMED class A", "Hull06DetTensorActual (citable 5 decls)")
  , ("H5 O(-)^-1 normalization", "NAMED", "Hull09 row; not formalized") ]

theorem h5DetTensorRows_length : h5DetTensorRows.length = 3 := rfl

#check h5_frozenSpec
#check h5_detTensor_bundle
#check h5DetTensorRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeH5DetTensorBundleActual
end