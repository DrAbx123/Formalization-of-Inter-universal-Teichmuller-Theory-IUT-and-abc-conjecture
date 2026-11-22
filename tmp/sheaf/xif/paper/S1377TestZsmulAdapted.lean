import tmp.sheaf.xif.paper.S1372XCoordinateFormulaActual
set_option maxHeartbeats 500000
noncomputable section
namespace Test3
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual
open WeierstrassCurve
variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

example (N : ℕ) (P0 : W.Point) : ((N + 1 : ℕ) : ℤ) • P0 = ((N : ℕ) : ℤ) • P0 + P0 := by
  exact SubNegMonoid.zsmul_succ' N P0

end Test3
