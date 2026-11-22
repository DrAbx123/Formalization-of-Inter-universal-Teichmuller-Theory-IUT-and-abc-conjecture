import tmp.sheaf.xif.paper.S3127GammaAlgebraActual
import tmp.sheaf.xif.paper.S3127GammaCompActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127GammaAlgebraActual
open LeanFormal.IUT.XiFPaper.S3127GammaCompActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127GammaCommActual
variable {K : Type} [Field K] {G : Type} [Group G]

/-- A G-action by automorphisms over Spec K. -/
structure S3127OverKAction (Y : SchemeOverField K) (G : Type) [Group G] where
  act : G →* Aut Y.left
  overK : ∀ g : G, (act g).hom ≫ Y.hom = Y.hom

/-- Target: the induced Gamma action fixes K-algebra constants. -/
def S3127FixesAlgebraMapTarget (Y : SchemeOverField K)
    (A : S3127OverKAction Y G) : Prop :=
  ∀ (g : G) (c : K),
    gammaAut (A.act g) (gammaAlgebraMap Y c) = gammaAlgebraMap Y c

theorem S3127FixesAlgebraMapTarget_holds
    (Y : SchemeOverField K) (A : S3127OverKAction Y G) :
    S3127FixesAlgebraMapTarget Y A := by
  intro g c
  have h := congrArg
    (fun k : Y.left ⟶ Spec (CommRingCat.of K) => Scheme.Γ.map k.op)
    (A.overK g)
  rw [op_comp, Scheme.Γ.map_comp] at h
  change ((Scheme.Γ.map Y.hom.op ≫
      Scheme.Γ.map (A.act g).hom.op).hom)
    (((Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom c) =
    (Scheme.Γ.map Y.hom.op).hom
      (((Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom c)
  rw [h]
theorem S3127FixesAlgebraMap_inverse
    (Y : SchemeOverField K) (A : S3127OverKAction Y G) (g : G) (c : K) :
    gammaAut ((A.act g).symm) (gammaAlgebraMap Y c) = gammaAlgebraMap Y c := by
  have hsymm : (A.act g).symm.hom ≫ Y.hom = Y.hom := by
    calc (A.act g).symm.hom ≫ Y.hom
        = (A.act g).inv ≫ Y.hom := rfl
      _ = (A.act g).inv ≫ ((A.act g).hom ≫ Y.hom) := by rw [A.overK g]
      _ = ((A.act g).inv ≫ (A.act g).hom) ≫ Y.hom := by rw [Category.assoc]
      _ = Y.hom := by rw [Iso.inv_hom_id, Category.id_comp]
  have h := congrArg
    (fun k : Y.left ⟶ Spec (CommRingCat.of K) => Scheme.Γ.map k.op) hsymm
  rw [op_comp, Scheme.Γ.map_comp] at h
  change ((Scheme.Γ.map Y.hom.op ≫
      Scheme.Γ.map (A.act g).symm.hom.op).hom)
    (((Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom c) =
    (Scheme.Γ.map Y.hom.op).hom
      (((Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom c)
  rw [h]

noncomputable def gammaSMulCommClass
    (Y : SchemeOverField K) (A : S3127OverKAction Y G) :
    letI := gammaMulSemiringAction A.act
    letI := gammaAlgebra Y
    SMulCommClass G K (Scheme.Γ.obj (Opposite.op Y.left)) := by
  letI := gammaMulSemiringAction A.act
  letI := gammaAlgebra Y
  refine ⟨fun g c x => ?_⟩
  change (gammaActionHom A.act g) (gammaAlgebraMap Y c * x) =
    gammaAlgebraMap Y c * (gammaActionHom A.act g) x
  rw [map_mul]
  change gammaAut ((A.act g).symm) (gammaAlgebraMap Y c) *
      (gammaActionHom A.act g) x =
    gammaAlgebraMap Y c * (gammaActionHom A.act g) x
  rw [S3127FixesAlgebraMap_inverse]

#check gammaSMulCommClass
#check S3127FixesAlgebraMap_inverse
#check S3127FixesAlgebraMapTarget_holds
#check S3127OverKAction
end LeanFormal.IUT.XiFPaper.S3127GammaCommActual
end
