import tmp.sheaf.xif.paper.S3128QuotientSheafStrongActual
import tmp.sheaf.xif.paper.S3128PrestackActual
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Iut
open LeanFormal.IUT.XiFPaper.S3128SheafTorsorActual
open LeanFormal.IUT.XiFPaper.S3128QuotientSheafObjActual
open LeanFormal.IUT.XiFPaper.S3128QuotientSheafStrongActual
open LeanFormal.IUT.XiFPaper.S3128FiberTypeActual
open LeanFormal.IUT.XiFPaper.S3128PrestackActual
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.S3128StrongBaseChangeFunctorActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F}
variable {U U' : SchemeOverField F} (f : U' ⟶ U)

noncomputable def S3128StrongBaseChangeFunctor :
    S3128ZMod2QuotientSheafObj (F := F) (X := X) U ⥤
      S3128ZMod2QuotientSheafObj (F := F) (X := X) U' where
  obj A := S3128ZMod2QuotientSheafObj.baseChange f A
  map {A B} φ :=
    { pointsIso :=
        S3128WhiskerLeftIso ((Over.map f).op) φ.pointsIso
      equivariant := by
        intro g
        apply NatTrans.ext
        funext V
        simp [S3128WhiskerLeftIso,
          S3128ZMod2QuotientSheafObj.baseChange,
          Functor.whiskerLeft_app]
        exact congrArg
          (fun e => e.app ((Over.map f).op.obj V))
          (φ.equivariant g)
      mapCompat := fun V p =>
        φ.mapCompat ((Over.map f).op.obj V) p }
  map_id A := by
    apply S3128StrongHom.ext
    · change
        S3128WhiskerLeftIso ((Over.map f).op)
          (show S3128StrongHom A A from 𝟙 A).pointsIso =
        (S3128StrongHom.id
          (S3128ZMod2QuotientSheafObj.baseChange f A)).pointsIso
      apply Iso.ext
      apply NatTrans.ext
      funext V
      change (S3128StrongHom.id A).pointsIso.hom.app
          ((Over.map f).op.obj V) =
        𝟙 ((S3128ZMod2QuotientSheafObj.baseChange f A).points.obj V)
      dsimp [S3128StrongHom.id,
        S3128ZMod2QuotientSheafObj.baseChange,
        S3128ZMod2SheafTorsor.baseChange]
      rfl
    · apply heq_of_eq
      funext V p
      apply Iso.ext
      change ((S3128StrongHom.id A).mapCompat
          ((Over.map f).op.obj V) p).hom =
        ((S3128StrongHom.id
          (S3128ZMod2QuotientSheafObj.baseChange f A)).mapCompat
            V p).hom
      dsimp [S3128StrongHom.id,
        S3128ZMod2QuotientSheafObj.baseChange,
        S3128ZMod2SheafTorsor.baseChange]
      rfl

  map_comp {A B C} (φ : A ⟶ B) (ψ : B ⟶ C) := by
    apply S3128StrongHom.ext
    · dsimp [S3128StrongHom.comp,
        S3128ZMod2QuotientSheafObj.baseChange,
        S3128ZMod2SheafTorsor.baseChange,
        S3128ZMod2SheafTorsor.pullbackPoints]
      change
        S3128WhiskerLeftIso ((Over.map f).op)
          (φ.pointsIso ≪≫ ψ.pointsIso) =
        S3128WhiskerLeftIso ((Over.map f).op) φ.pointsIso
          ≪≫ S3128WhiskerLeftIso ((Over.map f).op) ψ.pointsIso
      rw [S3128WhiskerLeftIso_trans]
    · apply heq_of_eq
      funext V p
      apply Iso.ext
      simp only [S3128StrongHom.comp,
        S3128ZMod2SheafTorsor.baseChange,
        S3128ZMod2SheafTorsor.pullbackPoints]
      rfl

#check S3128StrongBaseChangeFunctor
end LeanFormal.IUT.XiFPaper.S3128StrongBaseChangeFunctorActual