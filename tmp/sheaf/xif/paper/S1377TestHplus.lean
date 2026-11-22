import tmp.sheaf.xif.paper.S1372XCoordinateFormulaActual
set_option maxHeartbeats 500000
noncomputable section
namespace Test
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual
open WeierstrassCurve
variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

example {u v X Y : K} (n : ℤ) (P0 : W.Point) (hA : W.Nonsingular u v) (hB : W.Nonsingular X Y)
    (hmP : (n - 1) • P0 = WeierstrassCurve.Affine.Point.some u v hA)
    (hnP : n • P0 = WeierstrassCurve.Affine.Point.some X Y hB) :
    WeierstrassCurve.Affine.Point.some u v hA + P0 = WeierstrassCurve.Affine.Point.some X Y hB := by
  calc WeierstrassCurve.Affine.Point.some u v hA + P0
      = ((n - 1) • P0) + (1 : ℤ) • P0 := by rw [hmP, one_zsmul]
    _ = ((n - 1) + 1) • P0 := (add_zsmul (m := n - 1) (n := (1 : ℤ)) P0).symm
    _ = n • P0 := by rw [show n - 1 + 1 = n by ring]
    _ = WeierstrassCurve.Affine.Point.some X Y hB := hnP

end Test
