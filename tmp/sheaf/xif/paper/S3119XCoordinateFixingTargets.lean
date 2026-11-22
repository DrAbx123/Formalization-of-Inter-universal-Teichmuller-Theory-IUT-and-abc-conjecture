import tmp.sheaf.xif.paper.S3119WeierstrassFiltrationActual
import tmp.sheaf.xif.paper.S3119AutoClassificationTargets
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119WeierstrassFiltrationActual
open LeanFormal.IUT.XiFPaper.S3119AutoClassificationTargets
namespace LeanFormal.IUT.XiFPaper.S3119XCoordinateFixingTargets
set_option backward.isDefEq.respectTransparency false

variable {l : PrimeGeFive}

/-- Image of the weighted degree filtration in the coordinate ring. -/
noncomputable def S3119filtR (n : ℕ) : Set (S1348CoordinateRing l) :=
  Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l}) '' filt n

/-- Minimal target: every automorphism sends x into the degree-two filtered part. -/
def S3119XImageInFiltRTwoTarget : Prop :=
  ∀ φ : S1348CoordinateRing l ≃ₐ[S1348K l] S1348CoordinateRing l,
    φ (S3119x0 (l := l)) ∈ S3119filtR (l := l) 2

/-- Consequence shape: x maps linearly, φ(x) = a + b x. -/
def S3119XLinearTarget : Prop :=
  ∀ φ : S1348CoordinateRing l ≃ₐ[S1348K l] S1348CoordinateRing l,
    ∃ a b : S1348K l,
      φ (S3119x0 (l := l)) =
        algebraMap (S1348K l) (S1348CoordinateRing l) a + b • S3119x0 (l := l)

/-- Final x-fixing target. -/
def S3119XCoordinateFixingTarget₂ : Prop :=
  ∀ φ : S1348CoordinateRing l ≃ₐ[S1348K l] S1348CoordinateRing l,
    φ (S3119x0 (l := l)) = S3119x0 (l := l)

#check weightedDegree_X0
#check weightedDegree_X1
#check filt_two_le_span
#check S3119filtR
#check S3119XImageInFiltRTwoTarget
#check S3119XLinearTarget
#check S3119XCoordinateFixingTarget₂
end LeanFormal.IUT.XiFPaper.S3119XCoordinateFixingTargets
end
