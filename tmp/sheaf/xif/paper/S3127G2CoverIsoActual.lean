import tmp.sheaf.xif.paper.S3127G2QuotientObjActual
import tmp.sheaf.xif.paper.S3127GammaRAlgebraActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127GammaRAlgebraActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2CoverIsoActual
variable {l : PrimeGeFive}

noncomputable def S3127G2RawCoverA
    (A : S3127FiniteEtaleOverKFull l) :
    FiniteEtaleCover (S1419AffineScheme l) :=
  FiniteEtaleCover.mk (S := S1419AffineScheme l)
    A.obj.hom.left A.property.2 A.property.1

noncomputable def S3127G2AffineCoverA
    (A : S3127FiniteEtaleOverKFull l) :
    FiniteEtaleCover (S1419AffineScheme l) := by
  let R := S1348CoordinateRing l
  let Y := A.obj.left.left
  let hom := A.obj.hom.left
  haveI : IsAffine Y := S3127FullCover_isAffine A
  letI : Algebra R (Scheme.Γ.obj (Opposite.op Y)) := gammaAlgebraOf Y hom
  have halg : algebraMap R (Scheme.Γ.obj (Opposite.op Y)) =
    gammaAlgebraMapOf Y hom := rfl
  have hEt : Algebra.Etale R (Scheme.Γ.obj (Opposite.op Y)) :=
    gammaEtaleOf Y hom A.property.2 halg
  have hFin : Module.Finite R (Scheme.Γ.obj (Opposite.op Y)) :=
    gammaFiniteOf Y hom A.property.1 halg
  exact affineCover (R := R)
    (Scheme.Γ.obj (Opposite.op Y)) hEt hFin

noncomputable def S3127G2CoverIsoA
    (A : S3127FiniteEtaleOverKFull l) :
    S3127G2RawCoverA A ≅ S3127G2AffineCoverA A := by
  let R := S1348CoordinateRing l
  let Y := A.obj.left.left
  let hom := A.obj.hom.left
  haveI : IsAffine Y := S3127FullCover_isAffine A
  have hw : A.obj.left.left.isoSpec.hom ≫
      (S3127G2AffineCoverA A).obj.hom = (S3127G2RawCoverA A).obj.hom := by
    change A.obj.left.left.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (gammaAlgebraMapOf Y hom)) = hom
    exact gammaBridgeOf Y hom
  let eover : (S3127G2RawCoverA A).obj ≅ (S3127G2AffineCoverA A).obj :=
    Over.isoMk A.obj.left.left.isoSpec hw
  exact ObjectProperty.isoMk (P := fun X : Over (S1419AffineScheme l) => IsFiniteEtaleHom X.hom) eover

#check S3127G2CoverIsoA
end LeanFormal.IUT.XiFPaper.S3127G2CoverIsoActual
end