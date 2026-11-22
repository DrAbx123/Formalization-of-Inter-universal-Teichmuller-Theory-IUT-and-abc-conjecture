import tmp.sheaf.xif.paper.S3127G2CoverIsoActual
import tmp.sheaf.xif.paper.S3127G2QuotientMapRawActual
import tmp.sheaf.xif.paper.S3127G2QuotientObjActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127GammaCompActual
open LeanFormal.IUT.XiFPaper.S3127GammaRAlgebraActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2CoverIsoActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapRawActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientObjActual
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
variable {l : PrimeGeFive} {G : Type} [Group G] [Fintype G] [DecidableEq G]

noncomputable def S3127G2QuotientMap
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) :
    let R := S1348CoordinateRing l
    let Y := A.obj.left.left
    let hom := A.obj.hom.left
    letI := gammaAlgebraOf Y hom
    letI := gammaMulSemiringAction act.act
    letI := S3127GammaSMulCommClassOf A act
    letI : Algebra.Etale R (Scheme.Γ.obj (Opposite.op Y)) :=
      gammaEtaleOf Y hom A.property.2 (by rfl)
    letI : Module.Finite R (Scheme.Γ.obj (Opposite.op Y)) :=
      gammaFiniteOf Y hom A.property.1 (by rfl)
    let Qfull := affineQuotientCoverGeneral (R := R) (Scheme.Γ.obj (Opposite.op Y)) G
    A ⟶ S3127G2QuotientObj Qfull := by
  let R := S1348CoordinateRing l
  let Y := A.obj.left.left
  let hom := A.obj.hom.left
  letI := gammaAlgebraOf Y hom
  letI := gammaMulSemiringAction act.act
  letI := S3127GammaSMulCommClassOf A act
  letI : Algebra.Etale R (Scheme.Γ.obj (Opposite.op Y)) :=
    gammaEtaleOf Y hom A.property.2 (by rfl)
  letI : Module.Finite R (Scheme.Γ.obj (Opposite.op Y)) :=
    gammaFiniteOf Y hom A.property.1 (by rfl)
  let Qfull := affineQuotientCoverGeneral (R := R) (Scheme.Γ.obj (Opposite.op Y)) G
  let Qobj := S3127G2QuotientObj Qfull
  let raw := S3127G2QuotientMapRaw A act
  let g := raw.hom.left
  have hk : g ≫ Qobj.obj.left.hom = A.obj.left.hom := by
    change raw.hom.left ≫ (Qfull.obj.hom ≫ (S1419AffineOver l).hom) =
      A.obj.left.hom
    rw [← Category.assoc, Over.w raw.hom]
    change A.obj.hom.left ≫ (S1419AffineOver l).hom = A.obj.left.hom
    exact Over.w A.obj.hom
  let a : A.obj.left ⟶ Qobj.obj.left := Over.homMk g hk
  let fhom : A.obj ⟶ Qobj.obj := Over.homMk a (by
    apply Over.OverMorphism.ext
    change raw.hom.left ≫ Qfull.obj.hom = A.obj.hom.left
    rw [Over.w raw.hom]
    rfl)
  exact ObjectProperty.homMk fhom

#check S3127G2QuotientMap
end LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
end