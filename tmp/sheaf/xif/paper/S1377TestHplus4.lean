import tmp.sheaf.xif.paper.S1372XCoordinateFormulaActual
set_option maxHeartbeats 800000
noncomputable section
namespace Test5
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual
open WeierstrassCurve
variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

example (M : ℕ) (P0 : W.Point) :
    (((M + 3 : ℕ) : ℤ)) • P0 = (((M + 2 : ℕ) : ℤ)) • P0 + P0 := by
  rw [natCast_zsmul, natCast_zsmul]
  exact AddMonoid.nsmul_succ (M + 2) P0

example {u v X Y : K} (M : ℕ) (P0 : W.Point) (hA : W.Nonsingular u v) (hB : W.Nonsingular X Y)
    (hmP : (((M + 2 : ℕ) : ℤ)) • P0 = WeierstrassCurve.Affine.Point.some u v hA)
    (hnP : (((M + 3 : ℕ) : ℤ)) • P0 = WeierstrassCurve.Affine.Point.some X Y hB) :
    WeierstrassCurve.Affine.Point.some u v hA + P0 = WeierstrassCurve.Affine.Point.some X Y hB := by
  have h1 : (((M + 3 : ℕ) : ℤ)) • P0 = (((M + 2 : ℕ) : ℤ)) • P0 + P0 := by
    rw [natCast_zsmul, natCast_zsmul]
    exact AddMonoid.nsmul_succ (M + 2) P0
  calc WeierstrassCurve.Affine.Point.some u v hA + P0
      = (((M + 2 : ℕ) : ℤ)) • P0 + P0 := by rw [hmP]
    _ = (((M + 3 : ℕ) : ℤ)) • P0 := h1.symm
    _ = WeierstrassCurve.Affine.Point.some X Y hB := hnP

end Test5
