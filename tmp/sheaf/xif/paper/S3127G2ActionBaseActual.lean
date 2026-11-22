import tmp.sheaf.xif.paper.S3127KLinearFullActual
import tmp.sheaf.xif.paper.S3127GammaActionActual
import tmp.sheaf.xif.paper.S3127GammaRAlgebraActual
import tmp.sheaf.xif.paper.S3127GammaCompActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127GammaRAlgebraActual
open LeanFormal.IUT.XiFPaper.S3127GammaCompActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2RActionActual
variable {l : PrimeGeFive} {G : Type} [Group G]

structure S3127OverRAction
    (A : S3127FiniteEtaleOverKFull l) (G : Type) [Group G] where
  act : G →* Aut A.obj.left.left
  overR : ∀ g : G, (act g).hom ≫ A.obj.hom.left = A.obj.hom.left

theorem S3127FixesAlgebraMapOf
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
    (g : G) (c : S1348CoordinateRing l) :
    gammaAut (act.act g)
      (gammaAlgebraMapOf A.obj.left.left A.obj.hom.left c) =
    gammaAlgebraMapOf A.obj.left.left A.obj.hom.left c := by
  have h := congrArg
    (fun k : A.obj.left.left ⟶ Spec (CommRingCat.of (S1348CoordinateRing l)) =>
      Scheme.Γ.map k.op) (act.overR g)
  erw [op_comp, Scheme.Γ.map_comp] at h
  change ((Scheme.Γ.map A.obj.hom.left.op ≫
      Scheme.Γ.map (act.act g).hom.op).hom)
    (((Scheme.ΓSpecIso (CommRingCat.of (S1348CoordinateRing l))).inv).hom c) =
    (Scheme.Γ.map A.obj.hom.left.op).hom
      (((Scheme.ΓSpecIso (CommRingCat.of (S1348CoordinateRing l))).inv).hom c)
  exact congrArg
    (fun q : Scheme.Γ.obj (Opposite.op (Spec (CommRingCat.of (S1348CoordinateRing l)))) ⟶
        Scheme.Γ.obj (Opposite.op (A.obj.left.left)) =>
      q.hom ((Scheme.ΓSpecIso (CommRingCat.of (S1348CoordinateRing l))).inv.hom c)) h


theorem S3127FixesAlgebraMapOf_inverse
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
    (g : G) (c : S1348CoordinateRing l) :
    gammaAut ((act.act g).symm)
      (gammaAlgebraMapOf A.obj.left.left A.obj.hom.left c) =
    gammaAlgebraMapOf A.obj.left.left A.obj.hom.left c := by
  have hsymm : (act.act g).symm.hom ≫ A.obj.hom.left = A.obj.hom.left := by
    calc
      (act.act g).symm.hom ≫ A.obj.hom.left
          = (act.act g).inv ≫ A.obj.hom.left := rfl
      _ = (act.act g).inv ≫ ((act.act g).hom ≫ A.obj.hom.left) := by
            rw [act.overR g]
      _ = ((act.act g).inv ≫ (act.act g).hom) ≫ A.obj.hom.left := by
            rw [Category.assoc]
      _ = A.obj.hom.left := by rw [Iso.inv_hom_id, Category.id_comp]
  have h := congrArg
    (fun k : A.obj.left.left ⟶ Spec (CommRingCat.of (S1348CoordinateRing l)) =>
      Scheme.Γ.map k.op) hsymm
  erw [op_comp, Scheme.Γ.map_comp] at h
  change ((Scheme.Γ.map A.obj.hom.left.op ≫
      Scheme.Γ.map (act.act g).symm.hom.op).hom)
    (((Scheme.ΓSpecIso (CommRingCat.of (S1348CoordinateRing l))).inv).hom c) =
    (Scheme.Γ.map A.obj.hom.left.op).hom
      (((Scheme.ΓSpecIso (CommRingCat.of (S1348CoordinateRing l))).inv).hom c)
  exact congrArg
    (fun q : Scheme.Γ.obj (Opposite.op (Spec (CommRingCat.of (S1348CoordinateRing l)))) ⟶
        Scheme.Γ.obj (Opposite.op (A.obj.left.left)) =>
      q.hom ((Scheme.ΓSpecIso (CommRingCat.of (S1348CoordinateRing l))).inv.hom c)) h

#check S3127FixesAlgebraMapOf_inverse


noncomputable def S3127GammaSMulCommClassOf
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) :
    letI := gammaMulSemiringAction act.act
    letI := gammaAlgebraOf A.obj.left.left A.obj.hom.left
    SMulCommClass G (S1348CoordinateRing l)
      (Scheme.Γ.obj (Opposite.op (A.obj.left.left))) := by
  letI := gammaMulSemiringAction act.act
  letI := gammaAlgebraOf A.obj.left.left A.obj.hom.left
  refine ⟨fun g c x => ?_⟩
  change (gammaActionHom act.act g)
      (gammaAlgebraMapOf A.obj.left.left A.obj.hom.left c * x) =
    gammaAlgebraMapOf A.obj.left.left A.obj.hom.left c *
      (gammaActionHom act.act g) x
  rw [map_mul]
  change gammaAut ((act.act g).symm)
        (gammaAlgebraMapOf A.obj.left.left A.obj.hom.left c) *
      (gammaActionHom act.act g) x =
    gammaAlgebraMapOf A.obj.left.left A.obj.hom.left c *
      (gammaActionHom act.act g) x
  rw [S3127FixesAlgebraMapOf_inverse]

#check S3127GammaSMulCommClassOf

#check S3127OverRAction
#check S3127FixesAlgebraMapOf

noncomputable def S3127OverRAction_inv
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
    (g : G) :
    (act.act g).symm.hom ≫ A.obj.hom.left = A.obj.hom.left := by
  calc
    (act.act g).symm.hom ≫ A.obj.hom.left
        = (act.act g).inv ≫ A.obj.hom.left := rfl
    _ = (act.act g).inv ≫ ((act.act g).hom ≫ A.obj.hom.left) := by rw [act.overR g]
    _ = ((act.act g).inv ≫ (act.act g).hom) ≫ A.obj.hom.left := by rw [Category.assoc]
    _ = A.obj.hom.left := by rw [Iso.inv_hom_id, Category.id_comp]

noncomputable def S3127G2Action
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) :
    G → (A ⟶ A) :=
  fun g =>
    ObjectProperty.homMk
      (Over.homMk
        (Over.homMk (act.act g).symm.hom (by
          rw [← Over.w A.obj.hom, ← Category.assoc, S3127OverRAction_inv A act g]))
        (by
          apply Over.OverMorphism.ext
          exact S3127OverRAction_inv A act g))

theorem S3127G2Action_one
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) :
    S3127G2Action A act (1 : G) = 𝟙 A := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply Over.OverMorphism.ext
  change ((act.act 1).symm.hom) = 𝟙 _
  rw [map_one act.act]
  rfl

theorem S3127G2Action_mul
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
    (g h : G) :
    S3127G2Action A act (g * h) =
      S3127G2Action A act g ≫ S3127G2Action A act h := by
  apply ObjectProperty.hom_ext
  change (S3127G2Action A act (g * h)).hom =
    (S3127G2Action A act g).hom ≫ (S3127G2Action A act h).hom
  apply Over.OverMorphism.ext
  apply Over.OverMorphism.ext
  simp [S3127G2Action, act.act.map_mul, Aut.Aut_mul_def,
    Iso.trans_symm, Iso.trans_hom]

#check S3127G2Action_mul

