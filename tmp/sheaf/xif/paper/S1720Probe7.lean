import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
set_option backward.isDefEq.respectTransparency false
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section
namespace Probe7
variable {k K : Type*} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
  [DecidableEq (AlgebraicClosure k)] [DecidableEq (AlgebraicClosure K)]
example (W : WeierstrassCurve k)
    (P : ((W⁄K)⁄(AlgebraicClosure K)).Point) (hP : (6 : ℤ) • P = 0) :
    True := by
  classical
  letI : CommRing (AlgebraicClosure K) := (AlgebraicClosure.instField K).toCommRing
  change ((W⁄K)⁄(AlgebraicClosure K)).Point at P
  have hcurve : ((W⁄K)⁄(AlgebraicClosure K)) = (W⁄(AlgebraicClosure K)) := by
    change (W⁄K).map
      ((IsScalarTower.toAlgHom k K (AlgebraicClosure K) : K →ₐ[k] AlgebraicClosure K) :
        K →+* AlgebraicClosure K) = W⁄(AlgebraicClosure K)
    rw [WeierstrassCurve.Affine.map_baseChange]
  cases hcurve
  let e : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure K :=
    IsAlgClosure.equiv k (AlgebraicClosure k) (AlgebraicClosure K)
  let P0 := Affine.Point.map (W' := W) (e.symm : AlgebraicClosure K →ₐ[k] AlgebraicClosure k) P
  have hP0 : (6 : ℤ) • P0 = 0 := by
    dsimp only [P0]
    rw [← AddMonoidHom.map_zsmul, hP, AddMonoidHom.map_zero]
  trivial
end Probe7
