import tmp.sheaf.xif.paper.S3127G2UniversalDataOfLiftPreimageActual
import tmp.sheaf.xif.paper.S1348D6OrbicurveActual
import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127G2QuotientMapRawActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import tmp.sheaf.xif.paper.S3127G2QuotientMapRawCoherenceActual
import tmp.sheaf.xif.paper.S3127G2LiftGeneralUniqActual
import tmp.sheaf.xif.paper.S3127G2LiftGeneralFacConsumerActual
import tmp.sheaf.xif.paper.S3127G2CoverIsoNaturalActual
import tmp.sheaf.xif.paper.S3127G2HPhiConsumerActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3127GammaCompActual
open LeanFormal.IUT.XiFPaper.S3127GammaRAlgebraActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2TargetActual
open LeanFormal.IUT.XiFPaper.S3127G2CoverIsoActual
open LeanFormal.IUT.XiFPaper.S3127FullForgetActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataOfLiftActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataOfLiftPreimageActual
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapRawActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapRawCoherenceActual
open LeanFormal.IUT.XiFPaper.S3127G2LiftGeneralUniqActual
open LeanFormal.IUT.XiFPaper.S3127G2LiftGeneralFacConsumerActual
open LeanFormal.IUT.XiFPaper.S3127G2CoverIsoNaturalActual
open LeanFormal.IUT.XiFPaper.S3127G2HPhiConsumerActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2UniversalDataOfLiftFullActual
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
  letI := gammaMulSemiringAction act.act
  letI := S3127GammaSMulCommClassOf A act
  letI : Algebra.Etale R (Scheme.Γ.obj (Opposite.op Y)) :=
    gammaEtaleOf Y A.obj.hom.left A.property.2 (by rfl)
  letI : Module.Finite R (Scheme.Γ.obj (Opposite.op Y)) :=
    gammaFiniteOf Y A.obj.hom.left A.property.1 (by rfl)
  letI := gammaAlgebraOf Z B.obj.hom.left
  letI : Algebra.Etale R (Scheme.Γ.obj (Opposite.op Z)) :=
    gammaEtaleOf Z B.obj.hom.left B.property.2 (by rfl)
  letI : Module.Finite R (Scheme.Γ.obj (Opposite.op Z)) :=
    gammaFiniteOf Z B.obj.hom.left B.property.1 (by rfl)
  simp only [Functor.map_comp, Functor.map_preimage]
  change (S3127FullForget (l := l)).map (S3127G2QuotientMap A act) ≫
      (S3127FullForget (l := l)).map
        (S3127G2UniversalDataOfLift_lift A act hfree hInv B f hf) =
    (S3127FullForget (l := l)).map f
  have hpre :
      (S3127FullForget (l := l)).map
        (S3127G2UniversalDataOfLift_lift A act hfree hInv B f hf) =
        S3127G2UniversalDataOfLift_raw A act B f hf :=
    Functor.map_preimage (S3127FullForget (l := l))
      (X := (S3127FreeQuotientTargetOf A act hfree hInv).quotientObj)
      (Y := B)
      (S3127G2UniversalDataOfLift_raw A act B f hf)
  have hstep :
      (S3127FullForget (l := l)).map (S3127G2QuotientMap A act) ≫
        (S3127FullForget (l := l)).map
          (S3127G2UniversalDataOfLift_lift A act hfree hInv B f hf) =
        S3127G2QuotientMapRaw A act ≫
          S3127G2UniversalDataOfLift_raw A act B f hf := by
    rw [S3127FullForget_map_quotientMap]
    congr 1
  rw [hstep]
  rw [show S3127G2QuotientMapRaw A act =
      (S3127G2CoverIsoA A).hom ≫
        affineQuotientCoverMapGeneral (R := S1348CoordinateRing l)
          (Scheme.Γ.obj (Opposite.op A.obj.left.left)) G from rfl]
  unfold S3127G2UniversalDataOfLift_raw
  dsimp only
  convert (S3127G2CoverIso_natural f) using 2 <;>
    simp [Category.assoc, S3127G2LiftGeneralFacConsumer]

#check S3127G2UniversalDataOfLift_fac
end LeanFormal.IUT.XiFPaper.S3127G2UniversalDataOfLiftFullActual
end
