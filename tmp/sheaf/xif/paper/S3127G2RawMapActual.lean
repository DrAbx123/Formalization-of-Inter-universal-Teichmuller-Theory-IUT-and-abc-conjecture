import tmp.sheaf.xif.paper.S3127G2CoverIsoActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer

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
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2RawMapActual
variable {l : PrimeGeFive} {G : Type} [Group G] [Fintype G] [DecidableEq G]

noncomputable def S3127G2QuotientMapRaw
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
    S3127G2RawCoverA A ⟶
      affineQuotientCoverGeneral (R := R) (Scheme.Γ.obj (Opposite.op Y)) G := by
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
  exact (S3127G2CoverIsoA A).hom ≫
    affineQuotientCoverMapGeneral (R := R) (Scheme.Γ.obj (Opposite.op Y)) G

#check S3127G2QuotientMapRaw
end LeanFormal.IUT.XiFPaper.S3127G2RawMapActual
end