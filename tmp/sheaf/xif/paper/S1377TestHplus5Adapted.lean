import tmp.sheaf.xif.paper.S1372XCoordinateFormulaActual
set_option maxHeartbeats 800000
noncomputable section
namespace Test6
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual
open WeierstrassCurve
variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

example (M : ℕ) (P0 : W.Point) : True := by
  let n : ℤ := ((M + 3 : ℕ) : ℤ)
  have hsmul : n • P0 = (n - 1) • P0 + P0 := by
    rw [show n = (((M + 2) + 1 : ℕ) : ℤ) by dsimp [n]; push_cast; ring,
      show n - 1 = (((M + 2 : ℕ)) : ℤ) by dsimp [n]; push_cast; ring,
      natCast_zsmul, natCast_zsmul]
    exact AddMonoid.nsmul_succ (M + 2) P0
  trivial

end Test6
