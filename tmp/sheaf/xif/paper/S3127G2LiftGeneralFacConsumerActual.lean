import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtaleCoverFoundations
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2LiftGeneralFacConsumerActual
universe u
variable {R : Type u} [CommRing R]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable [MulSemiringAction G A] [SMulCommClass G R A]
variable [Algebra.Etale R A] [Module.Finite R A]
variable (hEtB : Algebra.Etale R B) (hFinB : Module.Finite R B)
variable (φ : B →ₐ[R] A)
variable (hφ : ∀ (g : G) (b : B), groupActionRingEquiv A G g (φ b) = φ b)

theorem S3127G2LiftGeneralFacConsumer :
    affineQuotientCoverMapGeneral (R := R) A G ≫
      affineQuotientCoverLiftGeneral
        (R := R) (A := A) (B := B) (G := G) hEtB hFinB φ hφ =
      affineCoverMapOfAlgHom
        (inferInstance : Algebra.Etale R A)
        (inferInstance : Module.Finite R A) hEtB hFinB φ :=
  affineQuotientCoverLiftGeneral_fac
    (R := R) (A := A) (B := B) (G := G) hEtB hFinB φ hφ

#check S3127G2LiftGeneralFacConsumer
end LeanFormal.IUT.XiFPaper.S3127G2LiftGeneralFacConsumerActual
end
