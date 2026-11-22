import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleFixedPointsGeneral
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2AffineQuotientCoverMapCompActual
universe u
variable {R : Type u} [CommRing R]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable [MulSemiringAction G A] [SMulCommClass G R A]
variable [Algebra.Etale R A] [Module.Finite R A]
variable (hEtB : Algebra.Etale R B) (hFinB : Module.Finite R B)

theorem affineQuotientCoverMapGeneral_comp
    (ψ : B →ₐ[R] fixedPointSubalgebra R A G) :
    affineQuotientCoverMapGeneral (R := R) A G ≫
      affineCoverMapOfAlgHom
        (FiniteEtaleFixedPointsGeneral.fixedPointSubalgebra_finiteEtale
          (R := R) (A := A) (G := G)).1
        (FiniteEtaleFixedPointsGeneral.fixedPointSubalgebra_finiteEtale
          (R := R) (A := A) (G := G)).2
        hEtB hFinB ψ =
      affineCoverMapOfAlgHom (R := R)
        (inferInstance : Algebra.Etale R A)
        (inferInstance : Module.Finite R A)
        hEtB hFinB
        ((Subalgebra.val (fixedPointSubalgebra R A G)).comp ψ) := by
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  unfold affineQuotientCoverMapGeneral affineCoverMapOfAlgHom
  change Spec.map (CommRingCat.ofHom
      (Subalgebra.val (fixedPointSubalgebra R A G))) ≫
      Spec.map (CommRingCat.ofHom
        (ψ : B →+* fixedPointSubalgebra R A G)) =
    Spec.map (CommRingCat.ofHom
      (((Subalgebra.val (fixedPointSubalgebra R A G)).comp ψ :
        B →ₐ[R] A) : B →+* A))
  rw [← Spec.map_comp]
  congr 1

#check affineQuotientCoverMapGeneral_comp
end LeanFormal.IUT.XiFPaper.S3127G2AffineQuotientCoverMapCompActual
end
