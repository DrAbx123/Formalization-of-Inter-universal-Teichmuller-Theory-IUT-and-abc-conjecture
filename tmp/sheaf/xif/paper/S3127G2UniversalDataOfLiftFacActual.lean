import tmp.sheaf.xif.paper.S3127G2UniversalDataOfLiftRawFacActual
import tmp.sheaf.xif.paper.S3127G2UniversalDataOfLiftPreimageActual
import tmp.sheaf.xif.paper.S3127G2UniversalDataOfLiftActual
import tmp.sheaf.xif.paper.S3127G2QuotientMapRawCoherenceActual
import tmp.sheaf.xif.paper.S3127G2CoverIsoNaturalActual
import tmp.sheaf.xif.paper.S3127G2HPhiConsumerActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2TargetActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapRawActual
open LeanFormal.IUT.XiFPaper.S3127G2CoverIsoActual
open LeanFormal.IUT.XiFPaper.S3127FullForgetActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataOfLiftPreimageActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataOfLiftRawFacActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataOfLiftActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapRawCoherenceActual
open LeanFormal.IUT.XiFPaper.S3127G2CoverIsoNaturalActual
open LeanFormal.IUT.XiFPaper.S3127G2HPhiConsumerActual
open LeanFormal.IUT.XiFPaper.S3127GammaRAlgebraActual
open LeanFormal.IUT.XiFPaper.S3127GammaCompActual
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2UniversalDataOfLiftFacActual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G] [DecidableEq G]
variable (hfree : ∀ (x : A.obj.left.left) (g : G),
  (S3127G2Action A act g).hom.left.left x = x → g = 1)
variable (hInv : ∀ g : G,
  S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act)
variable (B : S3127FiniteEtaleOverKFull l) (f : A ⟶ B)
variable (hf : ∀ g : G, S3127G2Action A act g ≫ f = f)

theorem S3127G2UniversalDataOfLift_fac :
    (S3127FreeQuotientTargetOf A act hfree hInv).quotientMap ≫
      S3127G2UniversalDataOfLift_lift A act hfree hInv B f hf = f := by
  apply (S3127FullForget_faithful (l := l)).map_injective
  let R := S1348CoordinateRing l
  let Y := A.obj.left.left
  let Z := B.obj.left.left
  letI := gammaAlgebraOf Y A.obj.hom.left
  letI := gammaAlgebraOf Z B.obj.hom.left
  letI := gammaMulSemiringAction act.act
  letI := S3127GammaSMulCommClassOf A act
  letI : Algebra.Etale R (Scheme.Γ.obj (Opposite.op Y)) :=
    gammaEtaleOf Y A.obj.hom.left A.property.2 (by rfl)
  letI : Module.Finite R (Scheme.Γ.obj (Opposite.op Y)) :=
    gammaFiniteOf Y A.obj.hom.left A.property.1 (by rfl)
  letI : Algebra.Etale R (Scheme.Γ.obj (Opposite.op Z)) :=
    gammaEtaleOf Z B.obj.hom.left B.property.2 (by rfl)
  letI : Module.Finite R (Scheme.Γ.obj (Opposite.op Z)) :=
    gammaFiniteOf Z B.obj.hom.left B.property.1 (by rfl)
  have hmap :
      (S3127FullForget (l := l)).map
        (S3127G2UniversalDataOfLift_lift A act hfree hInv B f hf) =
        S3127G2UniversalDataOfLift_raw A act B f hf :=
    Functor.map_preimage (S3127FullForget (l := l))
      (X := (S3127FreeQuotientTargetOf A act hfree hInv).quotientObj)
      (Y := B) (S3127G2UniversalDataOfLift_raw A act B f hf)
  rw [Functor.map_comp, hmap]
  change (S3127FullForget (l := l)).map (S3127G2QuotientMap A act) ≫
      S3127G2UniversalDataOfLift_raw A act B f hf =
    (S3127FullForget (l := l)).map f
  rw [S3127FullForget_map_quotientMap]

  unfold S3127G2UniversalDataOfLift_raw
  dsimp only
  rw [show S3127G2QuotientMapRaw A act =
      (S3127G2CoverIsoA A).hom ≫
        affineQuotientCoverMapGeneral (R := R)
          (Scheme.Γ.obj (Opposite.op Y)) G from rfl]
  try simp only [Category.assoc]
  simp only [← Category.assoc]
  rw [Category.assoc]
  rw [S3127G2UniversalDataOfLiftRaw_fac
    (gammaEtaleOf Y A.obj.hom.left A.property.2 (by rfl))
    (gammaFiniteOf Y A.obj.hom.left A.property.1 (by rfl))
    (gammaEtaleOf Z B.obj.hom.left B.property.2 (by rfl))
    (gammaFiniteOf Z B.obj.hom.left B.property.1 (by rfl))
    (gammaAlgHomOfFullHom f)
    (S3127G2HPhiConsumer act f hf)]
  rw [S3127G2CoverIso_natural f]
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

#check S3127G2UniversalDataOfLift_fac
end LeanFormal.IUT.XiFPaper.S3127G2UniversalDataOfLiftFacActual
end
