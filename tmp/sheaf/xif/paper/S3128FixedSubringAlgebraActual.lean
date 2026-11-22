import tmp.sheaf.xif.paper.S3128LocalAffineQuotientActual
import Mathlib.Algebra.Algebra.Basic

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3128FixedSubringAlgebraActual

open LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128LocalAffineQuotientActual

variable {G : Type} [Group G]
variable {A B : Type} [CommRing A] [MulSemiringAction G A]
  [CommRing B] [MulSemiringAction G B]

/-- Algebra structure on fixed subrings from an equivariant ring map. -/
noncomputable def S3128FixedSubringAlgebra
    (φ : A →+* B) (hφ : forall (g : G) (a : A), φ (g • a) = g • φ a) :
    Algebra (S3128FixedSubring G A) (S3128FixedSubring G B) :=
  (S3128FixedSubringMap (G := G) (A := A) (B := B) φ hφ).toAlgebra

/-- Its algebraMap is the fixed-subring map. -/
theorem S3128FixedSubringAlgebra_algebraMap
    (φ : A →+* B) (hφ : forall (g : G) (a : A), φ (g • a) = g • φ a) :
    letI := S3128FixedSubringAlgebra (G := G) (A := A) (B := B) φ hφ
    algebraMap (S3128FixedSubring G A) (S3128FixedSubring G B) =
      S3128FixedSubringMap (G := G) (A := A) (B := B) φ hφ := by
  letI := S3128FixedSubringAlgebra (G := G) (A := A) (B := B) φ hφ
  exact RingHom.algebraMap_toAlgebra _

#check S3128FixedSubringAlgebra
#check S3128FixedSubringAlgebra_algebraMap

end LeanFormal.IUT.XiFPaper.S3128FixedSubringAlgebraActual
end