import tmp.sheaf.xif.paper.S1596UniversalAffineZSMulActual
import tmp.sheaf.xif.paper.S1521OmegaInvariantCancellationActual
import tmp.sheaf.xif.paper.S1410BivariateOmegaActual
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
namespace WeierstrassCurve.Universal
theorem S1597UniversalOmegaNeg (n : ℤ) :
    curve.ω (-n) = curve.ω n + CC curve.a₁ * curve.φ n * curve.ψ n
      + CC curve.a₃ * curve.ψ n ^ 3 := by
  rw [← mul_cancel_left_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero (two_ne_zero (α := Poly)))]
  simp_rw [left_distrib, WeierstrassCurve.two_mul_ω, WeierstrassCurve.ψc_neg,
    WeierstrassCurve.ψ_neg, WeierstrassCurve.φ_neg]
  ring1
def S1597SmulYNeg : Prop :=
  ∀ n : ℤ, n ≠ 0 →
    smulY (-n) =
      (curve.map (algebraMap (MvPolynomial Coeff ℤ) Field)).toAffine.negY
        (smulX n) (smulY n)
def S1597SmulXSubSmulX : Prop :=
  ∀ m n : ℤ, m ≠ 0 → n ≠ 0 →
    smulX m - smulX n =
      ψᵤ (n + m) * ψᵤ (n - m) / (ψᵤ n * ψᵤ m) ^ 2
end WeierstrassCurve.Universal
end
