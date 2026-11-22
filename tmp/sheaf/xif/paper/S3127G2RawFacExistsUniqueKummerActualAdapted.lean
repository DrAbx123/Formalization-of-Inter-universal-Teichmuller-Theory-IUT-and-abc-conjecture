import tmp.sheaf.xif.paper.S3127G2AffineLiftExistsUniqueActual
import tmp.sheaf.xif.paper.S3127G2CoverIsoNaturalActual
import tmp.sheaf.xif.paper.S3127G2QuotientMapRawCoherenceActual
import tmp.sheaf.xif.paper.S3127G2TargetActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127G2HPhiConsumerActual
import tmp.sheaf.xif.paper.S3127G2UniversalDataOfLiftRawFacActual
import tmp.sheaf.xif.paper.S3127G2GammaAlgHomActual
import tmp.sheaf.xif.paper.S3127G2GammaInvariantInterfaceActual
import tmp.sheaf.xif.paper.S3127FullForgetActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2TargetActual
open LeanFormal.IUT.XiFPaper.S3127G2CoverIsoActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapRawCoherenceActual
open LeanFormal.IUT.XiFPaper.S3127G2AffineLiftExistsUniqueActual
open LeanFormal.IUT.XiFPaper.S3127G2CoverIsoNaturalActual
open LeanFormal.IUT.XiFPaper.S3127G2HPhiConsumerActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataOfLiftRawFacActual
open LeanFormal.IUT.XiFPaper.S3127G2GammaAlgHomActual
open LeanFormal.IUT.XiFPaper.S3127G2GammaInvariantInterfaceActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127FullForgetActual
open LeanFormal.IUT.XiFPaper.S3127GammaRAlgebraActual
open LeanFormal.IUT.XiFPaper.S3127GammaCompActual
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapRawActual
open LeanFormal.IUT.XiFPaper.S3127G2LiftGeneralUniqActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2RawFacExistsUniqueKummerActualAdapted
variable {l : PrimeGeFive} {G : Type} [Group G] [Fintype G] [DecidableEq G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable (hfree : ∀ (x : A.obj.left.left) (g : G),
  (S3127G2Action A act g).hom.left.left x = x → g = 1)
variable (hInv : ∀ g : G,
  S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act)

theorem S3127G2RawFac_existsUnique
    (B : S3127FiniteEtaleOverKFull l) (f : A ⟶ B)
    (hf : ∀ g : G, S3127G2Action A act g ≫ f = f) :
    ∃! v_raw : (S3127FullForget (l := l)).obj
        (S3127FreeQuotientTargetOf A act hfree hInv).quotientObj ⟶
      (S3127FullForget (l := l)).obj B,
      (S3127FullForget (l := l)).map
        (S3127FreeQuotientTargetOf A act hfree hInv).quotientMap ≫ v_raw =
        (S3127FullForget (l := l)).map f := by
  have hbase : baseSpec (R := S1348CoordinateRing l) =
      S1419AffineScheme l := rfl
  cases hbase
  let R := S1348CoordinateRing l
  let Y := A.obj.left.left
  let Z := B.obj.left.left
  letI hAlgA : Algebra R (Scheme.Γ.obj (Opposite.op Y)) := gammaAlgebraOf (R := R) Y A.obj.hom.left
  letI hAlgB : Algebra R (Scheme.Γ.obj (Opposite.op Z)) := gammaAlgebraOf (R := R) Z B.obj.hom.left
  letI := gammaMulSemiringAction act.act
  letI := S3127GammaSMulCommClassOf A act
  letI hEtA : Algebra.Etale R (Scheme.Γ.obj (Opposite.op Y)) :=
    gammaEtaleOf (R := R) Y A.obj.hom.left A.property.2 (by rfl)
  letI hFinA : Module.Finite R (Scheme.Γ.obj (Opposite.op Y)) :=
    gammaFiniteOf (R := R) Y A.obj.hom.left A.property.1 (by rfl)
  letI hEtB : Algebra.Etale R (Scheme.Γ.obj (Opposite.op Z)) :=
    gammaEtaleOf (R := R) Z B.obj.hom.left B.property.2 (by rfl)
  letI hFinB : Module.Finite R (Scheme.Γ.obj (Opposite.op Z)) :=
    gammaFiniteOf (R := R) Z B.obj.hom.left B.property.1 (by rfl)
  let u := affineQuotientCoverLiftGeneral (R := R)
    (A := Scheme.Γ.obj (Opposite.op Y)) (B := Scheme.Γ.obj (Opposite.op Z)) (G := G)
    hEtB hFinB (gammaAlgHomOfFullHom f) (S3127G2HPhiConsumer act f hf)
  have hrawA : (S3127FullForget (l := l)).obj A = S3127G2RawCoverA A := rfl
  have hrawB : (S3127FullForget (l := l)).obj B = S3127G2RawCoverA B := rfl
  let alpha : (S3127FullForget (l := l)).obj A ≅ S3127G2AffineCoverA A :=
    hrawA ▸ S3127G2CoverIsoA A
  let beta : (S3127FullForget (l := l)).obj B ≅ S3127G2AffineCoverA B :=
    hrawB ▸ S3127G2CoverIsoA B
  have hq : (S3127FullForget (l := l)).map
      (S3127FreeQuotientTargetOf A act hfree hInv).quotientMap =
      S3127G2QuotientMapRaw A act := by
    change (S3127FullForget (l := l)).map (S3127G2QuotientMap A act) = _
    exact S3127FullForget_map_quotientMap
  have hnat : alpha.hom ≫ affineCoverMapOfAlgHom
      (gammaEtaleOf (R := R) Y A.obj.hom.left A.property.2 (by rfl))
      (gammaFiniteOf (R := R) Y A.obj.hom.left A.property.1 (by rfl))
      (gammaEtaleOf (R := R) Z B.obj.hom.left B.property.2 (by rfl))
      (gammaFiniteOf (R := R) Z B.obj.hom.left B.property.1 (by rfl))
      (gammaAlgHomOfFullHom f) =
      (S3127FullForget (l := l)).map f ≫ beta.hom := by
    simpa [alpha, beta] using (S3127G2CoverIso_natural f)
  refine ⟨u ≫ beta.inv, ?_, ?_⟩
  · calc
      (S3127FullForget (l := l)).map
          (S3127FreeQuotientTargetOf A act hfree hInv).quotientMap ≫
          (u ≫ beta.inv)
          = S3127G2QuotientMapRaw A act ≫ (u ≫ beta.inv) := by rw [hq]
      _ = (alpha.hom ≫ affineQuotientCoverMapGeneral (R := R)
              (Scheme.Γ.obj (Opposite.op Y)) G) ≫ (u ≫ beta.inv) := by
            rfl
      _ = alpha.hom ≫ (affineQuotientCoverMapGeneral (R := R)
              (Scheme.Γ.obj (Opposite.op Y)) G ≫ u) ≫ beta.inv := by
            simp only [Category.assoc]
      _ = alpha.hom ≫ (affineCoverMapOfAlgHom
              (gammaEtaleOf (R := R) Y A.obj.hom.left A.property.2 (by rfl))
              (gammaFiniteOf (R := R) Y A.obj.hom.left A.property.1 (by rfl))
              (gammaEtaleOf (R := R) Z B.obj.hom.left B.property.2 (by rfl))
              (gammaFiniteOf (R := R) Z B.obj.hom.left B.property.1 (by rfl))
              (gammaAlgHomOfFullHom f)) ≫ beta.inv := by
            rw [S3127G2UniversalDataOfLiftRaw_fac]
      _ = ((S3127FullForget (l := l)).map f ≫ beta.hom) ≫ beta.inv := by
            rw [← Category.assoc]
            convert hnat using 2 <;> simp [hrawA, hrawB]
      _ = (S3127FullForget (l := l)).map f := by
            rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · intro w hw
    have hL : alpha.hom ≫ (affineQuotientCoverMapGeneral (R := R)
        (Scheme.Γ.obj (Opposite.op Y)) G ≫ (w ≫ beta.hom)) =
        alpha.hom ≫ affineCoverMapOfAlgHom
          (gammaEtaleOf (R := R) Y A.obj.hom.left A.property.2 (by rfl))
          (gammaFiniteOf (R := R) Y A.obj.hom.left A.property.1 (by rfl))
          (gammaEtaleOf (R := R) Z B.obj.hom.left B.property.2 (by rfl))
          (gammaFiniteOf (R := R) Z B.obj.hom.left B.property.1 (by rfl))
          (gammaAlgHomOfFullHom f) := by
      calc
        alpha.hom ≫ (affineQuotientCoverMapGeneral (R := R)
            (Scheme.Γ.obj (Opposite.op Y)) G ≫ (w ≫ beta.hom))
            = (alpha.hom ≫ affineQuotientCoverMapGeneral (R := R)
                (Scheme.Γ.obj (Opposite.op Y)) G) ≫ (w ≫ beta.hom) := by
              rw [← Category.assoc]
        _ = S3127G2QuotientMapRaw A act ≫ (w ≫ beta.hom) := by rfl
        _ = ((S3127FullForget (l := l)).map
              (S3127FreeQuotientTargetOf A act hfree hInv).quotientMap) ≫
              (w ≫ beta.hom) := by rw [← hq]
        _ = (((S3127FullForget (l := l)).map
              (S3127FreeQuotientTargetOf A act hfree hInv).quotientMap) ≫ w) ≫
              beta.hom := by rw [← Category.assoc]
        _ = (S3127FullForget (l := l)).map f ≫ beta.hom := by rw [hw]
        _ = alpha.hom ≫ affineCoverMapOfAlgHom
              (gammaEtaleOf (R := R) Y A.obj.hom.left A.property.2 (by rfl))
              (gammaFiniteOf (R := R) Y A.obj.hom.left A.property.1 (by rfl))
              (gammaEtaleOf (R := R) Z B.obj.hom.left B.property.2 (by rfl))
              (gammaFiniteOf (R := R) Z B.obj.hom.left B.property.1 (by rfl))
              (gammaAlgHomOfFullHom f) := by
            convert hnat.symm using 2 <;> simp [hrawA, hrawB]
    have hcancel : affineQuotientCoverMapGeneral (R := R)
        (Scheme.Γ.obj (Opposite.op Y)) G ≫ (w ≫ beta.hom) =
        affineCoverMapOfAlgHom
          (gammaEtaleOf (R := R) Y A.obj.hom.left A.property.2 (by rfl))
          (gammaFiniteOf (R := R) Y A.obj.hom.left A.property.1 (by rfl))
          (gammaEtaleOf (R := R) Z B.obj.hom.left B.property.2 (by rfl))
          (gammaFiniteOf (R := R) Z B.obj.hom.left B.property.1 (by rfl))
          (gammaAlgHomOfFullHom f) := by
      have := congrArg (fun k => alpha.inv ≫ k) hL
      simpa [Category.assoc, Iso.inv_hom_id_assoc] using this
    have hu' : w ≫ beta.hom = u := affineQuotientCoverLiftGeneral_uniq
      (R := R) (A := Scheme.Γ.obj (Opposite.op Y))
      (B := Scheme.Γ.obj (Opposite.op Z)) (G := G)
      hEtA hFinA hEtB hFinB (gammaAlgHomOfFullHom f)
      (S3127G2HPhiConsumer act f hf) (w ≫ beta.hom) hcancel
    calc w = (w ≫ beta.hom) ≫ beta.inv := by
            rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = u ≫ beta.inv := congrArg (fun k => k ≫ beta.inv) hu'

#check S3127G2RawFac_existsUnique
end LeanFormal.IUT.XiFPaper.S3127G2RawFacExistsUniqueKummerActualAdapted
end
