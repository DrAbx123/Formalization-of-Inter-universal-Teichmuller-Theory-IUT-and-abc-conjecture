import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleFixedPointsGeneral
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
namespace LeanFormal.IUT.XiFPaper.S3127G2QFullAffineCoverEqActual
universe u
variable {R : Type u} [CommRing R]
variable {A : Type u} [CommRing A] [Algebra R A]
variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable [MulSemiringAction G A] [SMulCommClass G R A]
variable [Algebra.Etale R A] [Module.Finite R A]

theorem S3127G2QFullAffineCoverEq :
    affineQuotientCoverGeneral (R := R) A G =
      affineCover (fixedPointSubalgebra R A G)
        (FiniteEtaleFixedPointsGeneral.fixedPointSubalgebra_finiteEtale
          (R := R) (A := A) (G := G)).1
        (FiniteEtaleFixedPointsGeneral.fixedPointSubalgebra_finiteEtale
          (R := R) (A := A) (G := G)).2 :=
  rfl

#check S3127G2QFullAffineCoverEq
end LeanFormal.IUT.XiFPaper.S3127G2QFullAffineCoverEqActual
end
