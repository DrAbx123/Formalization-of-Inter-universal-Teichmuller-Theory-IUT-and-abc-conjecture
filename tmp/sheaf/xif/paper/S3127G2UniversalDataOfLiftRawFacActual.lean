import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
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
namespace LeanFormal.IUT.XiFPaper.S3127G2UniversalDataOfLiftRawFacActual
universe u
variable {R : Type u} [CommRing R]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable [MulSemiringAction G A] [SMulCommClass G R A]
variable (hEtA : Algebra.Etale R A) (hFinA : Module.Finite R A)
variable (hEtB : Algebra.Etale R B) (hFinB : Module.Finite R B)
variable (φ : B →ₐ[R] A)
variable (hφ : ∀ (g : G) (b : B), groupActionRingEquiv A G g (φ b) = φ b)

theorem S3127G2UniversalDataOfLiftRaw_fac :
    affineQuotientCoverMapGeneral (R := R) A G ≫
      affineQuotientCoverLiftGeneral hEtB hFinB φ hφ =
      affineCoverMapOfAlgHom hEtA hFinA hEtB hFinB φ :=
  affineQuotientCoverLiftGeneral_fac hEtB hFinB φ hφ

#check S3127G2UniversalDataOfLiftRaw_fac
end LeanFormal.IUT.XiFPaper.S3127G2UniversalDataOfLiftRawFacActual
end
