import tmp.sheaf.xif.paper.S3127G2LiftGeneralFacConsumerActual
import tmp.sheaf.xif.paper.S3127G2LiftGeneralUniqActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.XiFPaper.S3127G2LiftGeneralFacConsumerActual
open LeanFormal.IUT.XiFPaper.S3127G2LiftGeneralUniqActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S3127G2AffineLiftExistsUniqueActual
universe u
variable {R : Type u} [CommRing R]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable [MulSemiringAction G A] [SMulCommClass G R A]
variable [Algebra.Etale R A] [Module.Finite R A]

theorem S3127G2AffineLift_existsUnique
    (hEtA : Algebra.Etale R A) (hFinA : Module.Finite R A)
    (hEtB : Algebra.Etale R B) (hFinB : Module.Finite R B)
    (φ : B →ₐ[R] A)
    (hφ : ∀ (g : G) (b : B), groupActionRingEquiv A G g (φ b) = φ b) :
    ∃! u : affineQuotientCoverGeneral (R := R) A G ⟶
        affineCover (R := R) B hEtB hFinB,
      affineQuotientCoverMapGeneral (R := R) A G ≫ u =
        affineCoverMapOfAlgHom (R := R) (A := A) (B := B)
          hEtA hFinA hEtB hFinB φ := by
  refine ⟨affineQuotientCoverLiftGeneral (R := R) (A := A) (B := B) (G := G)
    hEtB hFinB φ hφ, ?_, ?_⟩
  · exact affineQuotientCoverLiftGeneral_fac (R := R) (A := A) (B := B) (G := G)
      hEtB hFinB φ hφ
  · intro u hu
    exact affineQuotientCoverLiftGeneral_uniq (R := R) (A := A) (B := B) (G := G)
      hEtA hFinA hEtB hFinB φ hφ u hu

#check S3127G2AffineLift_existsUnique
end LeanFormal.IUT.XiFPaper.S3127G2AffineLiftExistsUniqueActual
end