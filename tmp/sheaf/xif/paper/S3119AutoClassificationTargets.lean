import tmp.sheaf.xif.paper.S3119OverAutoAlgHomActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionAttempt
open LeanFormal.IUT.XiFPaper.S3119OverAutoAlgHomActual
namespace LeanFormal.IUT.XiFPaper.S3119AutoClassificationTargets
set_option backward.isDefEq.respectTransparency false

variable {l : PrimeGeFive}

/-- The class of x in the coordinate ring. -/
noncomputable abbrev S3119x0 : S1348CoordinateRing l :=
  Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l}) (MvPolynomial.X 0)

/-- The class of y in the coordinate ring. -/
noncomputable abbrev S3119y0 : S1348CoordinateRing l :=
  Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l}) (MvPolynomial.X 1)

/-- Minimal target 1: every K-algebra automorphism fixes the x-coordinate. -/
def S3119XCoordinateFixingTarget : Prop :=
  ∀ φ : S1348CoordinateRing l ≃ₐ[S1348K l] S1348CoordinateRing l,
    φ (S3119x0 (l := l)) = S3119x0 (l := l)

/-- Minimal target 2: every K-algebra automorphism preserves the two y-choices. -/
def S3119YChoiceTarget : Prop :=
  ∀ φ : S1348CoordinateRing l ≃ₐ[S1348K l] S1348CoordinateRing l,
    φ (S3119y0 (l := l)) = S3119y0 (l := l) ∨
      φ (S3119y0 (l := l)) = -S3119y0 (l := l) - S3119x0 (l := l)

/-- The remaining algebraic classification target. -/
def S3119AutIdOrNegTarget : Prop :=
  ∀ φ : S1348CoordinateRing l ≃ₐ[S1348K l] S1348CoordinateRing l,
    φ = AlgEquiv.refl ∨ φ = S3119NegInvolutionAlgEquiv (l := l)

#check S1348PointAlgHom_X0
#check S1348PointAlgHom_X1
#check S1348_aeval_affinePolynomial
#check S1348_aeval_affinePolynomial_eq_zero
#check S3119NegPolyHom_X0
#check S3119NegPolyHom_X1
#check S3119NegQuotientHom_mk

#check S3119XCoordinateFixingTarget
#check S3119YChoiceTarget
#check S3119AutIdOrNegTarget
end LeanFormal.IUT.XiFPaper.S3119AutoClassificationTargets
end
