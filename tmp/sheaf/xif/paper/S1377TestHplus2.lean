import tmp.sheaf.xif.paper.S1372XCoordinateFormulaActual
set_option maxHeartbeats 500000
noncomputable section
namespace Test2
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual
open WeierstrassCurve
variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

example {u v X Y : K} (n : ℤ) (P0 : W.Point) (hA : W.Nonsingular u v) (hB : W.Nonsingular X Y)
    (hmP : (n - 1) • P0 = WeierstrassCurve.Affine.Point.some u v hA)
    (hnP : n • P0 = WeierstrassCurve.Affine.Point.some X Y hB) :
    WeierstrassCurve.Affine.Point.some u v hA + P0 = WeierstrassCurve.Affine.Point.some X Y hB := by
  have hsub : (n - 1) • P0 = n • P0 - P0 := by
    rw [sub_one_zsmul, sub_eq_add_neg]
  have h1 : (n - 1) • P0 + P0 = n • P0 := by
    rw [hsub, sub_add_cancel]
  calc WeierstrassCurve.Affine.Point.some u v hA + P0
      = ((n - 1) • P0) + P0 := by rw [hmP]
    _ = n • P0 := h1
    _ = WeierstrassCurve.Affine.Point.some X Y hB := hnP

end Test2
