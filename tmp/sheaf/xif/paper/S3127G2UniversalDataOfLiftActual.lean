import tmp.sheaf.xif.paper.S3127G2GammaInvariantInterfaceActual
import tmp.sheaf.xif.paper.S3127GammaActionActual
import tmp.sheaf.xif.paper.S3127GammaCompActual
import tmp.sheaf.xif.paper.S1348D6OrbicurveActual
import tmp.sheaf.xif.paper.S3127GammaRAlgebraActual
import tmp.sheaf.xif.paper.S3127G2TargetActual
import tmp.sheaf.xif.paper.S3127G2CoverIsoActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127FullForgetActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2TargetActual
open LeanFormal.IUT.XiFPaper.S3127G2CoverIsoActual
open LeanFormal.IUT.XiFPaper.S3127FullForgetActual
open LeanFormal.IUT.XiFPaper.S3127G2GammaAlgHomActual
open LeanFormal.IUT.XiFPaper.S3127G2GammaInvariantInterfaceActual
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127GammaCompActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3127GammaRAlgebraActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2UniversalDataOfLiftActual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G] [DecidableEq G]
variable (hfree : ∀ (x : A.obj.left.left) (g : G),
  (S3127G2Action A act g).hom.left.left x = x → g = 1)
variable (hInv : ∀ g : G,
  S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act)
variable (B : S3127FiniteEtaleOverKFull l) (f : A ⟶ B)
variable (hf : ∀ g : G, S3127G2Action A act g ≫ f = f)

/-- Raw lift from the general affine quotient universal property, transported
to the raw cover of `B`. -/
noncomputable def S3127G2UniversalDataOfLift_raw :
    S3127G2QFull A act ⟶ S3127G2RawCoverA B := by
  let R := S1348CoordinateRing l
  let Y := A.obj.left.left
  let Z := B.obj.left.left
  letI := gammaAlgebraOf Y A.obj.hom.left
  letI := gammaMulSemiringAction act.act
  letI := S3127GammaSMulCommClassOf A act
  letI : Algebra.Etale R (Scheme.Γ.obj (Opposite.op Y)) := gammaEtaleOf Y A.obj.hom.left A.property.2 (by rfl)
  letI : Module.Finite R (Scheme.Γ.obj (Opposite.op Y)) := gammaFiniteOf Y A.obj.hom.left A.property.1 (by rfl)
  letI : Algebra R (Scheme.Γ.obj (Opposite.op Z)) := gammaAlgebraOf Z B.obj.hom.left
  letI : Algebra.Etale R (Scheme.Γ.obj (Opposite.op Z)) := gammaEtaleOf Z B.obj.hom.left B.property.2 (by rfl)
  letI : Module.Finite R (Scheme.Γ.obj (Opposite.op Z)) := gammaFiniteOf Z B.obj.hom.left B.property.1 (by rfl)
  let φ := gammaAlgHomOfFullHom f
  let hφ := gammaAlgHomOfFullHom_invariant act f hf
  let u := affineQuotientCoverLiftGeneral (R := R)
    (A := Scheme.Γ.obj (Opposite.op Y))
    (B := Scheme.Γ.obj (Opposite.op Z)) (G := G)
    (by infer_instance : Algebra.Etale R (Scheme.Γ.obj (Opposite.op Z)))
    (by infer_instance : Module.Finite R (Scheme.Γ.obj (Opposite.op Z))) φ hφ
  exact u ≫ (S3127G2CoverIsoA B).inv

#check S3127G2UniversalDataOfLift_raw
end LeanFormal.IUT.XiFPaper.S3127G2UniversalDataOfLiftActual
end
