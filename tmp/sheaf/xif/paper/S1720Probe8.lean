import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
set_option backward.isDefEq.respectTransparency false
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section
namespace Probe8
variable {F : Type*} [Field F] [DecidableEq F]
def pc {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) : W₁.toAffine.Point → W₂.toAffine.Point :=
  fun P => h ▸ P
theorem pc_nsmul {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) (n : ℕ) (P : W₁.toAffine.Point) :
    pc h (n • P) = n • pc h P := by
  cases h
  rfl
theorem pc_zsmul {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) (n : ℤ) (P : W₁.toAffine.Point) :
    pc h (n • P) = n • pc h P := by
  cases h
  rfl
theorem pc_inj {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) : Function.Injective (pc h) := by
  cases h
  exact fun _ _ h => h
end Probe8
