import tmp.sheaf.xif.paper.S1348D6OrbicurveActual
import tmp.sheaf.xif.paper.S3119WeierstrassFiltrationActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
namespace LeanFormal.IUT.XiFPaper.S3119ProjectiveInfinityActual
set_option backward.isDefEq.respectTransparency false

variable {l : PrimeGeFive}

/-- The point at infinity of the projective closure of S1348: Mathlib's
projective zero point. -/
noncomputable def S3119InfinityPoint :
    (S1348Curve l).toProjective.Point :=
  0

theorem S3119InfinityPoint_is_zero :
    S3119InfinityPoint (l := l) =
      (0 : (S1348Curve l).toProjective.Point) := rfl

/-- No affine K-point maps to the point at infinity: the punctured affine points
are exactly the complement of infinity. -/
theorem S3119_affineEval_ne_infinity
    (ψ : S1348CoordinateRing l →ₐ[S1348K l] S1348K l) :
    S1348EvalPoint l ψ ≠ S3119InfinityPoint (l := l) := by
  rw [S3119InfinityPoint_is_zero]
  exact S1348EvalPoint_ne_zero l ψ

/-- Target: every affine coordinate-ring automorphism extends to a projective
point map fixing the point at infinity.  This is the precise "β preserves ∞"
statement needed for the filtration argument. -/
def S3119ProjectivePointActionTarget : Prop :=
  ∀ φ : S1348CoordinateRing l ≃ₐ[S1348K l] S1348CoordinateRing l,
    ∃ σ : (S1348Curve l).toProjective.Point → (S1348Curve l).toProjective.Point,
      σ (S3119InfinityPoint (l := l)) = S3119InfinityPoint (l := l) ∧
      ∀ ψ : S1348CoordinateRing l →ₐ[S1348K l] S1348K l,
        σ (S1348EvalPoint l ψ) =
          S1348EvalPoint l (ψ.comp φ.toAlgHom)

#check S1348EvalPoint
#check S1348EvalPoint_ne_zero
#check S1348PointAlgHom_surjective
#check WeierstrassCurve.Projective.Point.fromAffine
#check WeierstrassCurve.Projective.Point.toAffine
#check WeierstrassCurve.Projective.Point.toAffineAddEquiv
#check S3119InfinityPoint
#check S3119_affineEval_ne_infinity
#check S3119ProjectivePointActionTarget
end LeanFormal.IUT.XiFPaper.S3119ProjectiveInfinityActual
end
