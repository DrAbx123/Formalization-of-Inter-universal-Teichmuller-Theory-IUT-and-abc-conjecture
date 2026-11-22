import tmp.sheaf.xif.paper.S3128ZMod2BaseChangeActual
import Mathlib.CategoryTheory.Comma.Over.Basic
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Iut
open LeanFormal.IUT.XiFPaper.S3128ZMod2FiberCategoryActual
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.S3128SheafTorsorActual
variable {F : Type} [Field F]

/-- A Z/2-torsor as a presheaf of points on `Over U`, with a free transitive
Z/2-action on sections. -/
structure S3128ZMod2SheafTorsor (U : SchemeOverField F) where
  points : (Over U)ᵒᵖ ⥤ Type
  action : Multiplicative (ZMod 2) →* CategoryTheory.End points
  torsor :
    ∀ (V : (Over U)ᵒᵖ) (p q : points.obj V),
      ∃! g : Multiplicative (ZMod 2),
        (action g).app V p = q

variable {U U' : SchemeOverField F} (f : U' ⟶ U)

/-- Base change by precomposition of the test object. -/
noncomputable def S3128ZMod2SheafTorsor.pullbackPoints
    (A : S3128ZMod2SheafTorsor (F := F) U) :
    (Over U')ᵒᵖ ⥤ Type :=
  (Over.map f).op ⋙ A.points

noncomputable def S3128ZMod2SheafTorsor.baseChange
    (A : S3128ZMod2SheafTorsor (F := F) U) :
    S3128ZMod2SheafTorsor (F := F) U' where
  points := S3128ZMod2SheafTorsor.pullbackPoints f A
  action := by
    letI := A.action
    -- precomposition of endomorphisms
    exact
      { toFun := fun g =>
          { app := fun V => (A.action g).app ((Over.map f).op.obj V)
            naturality := by
              intro V W φ
              exact (A.action g).naturality ((Over.map f).op.map φ) }
        map_one' := by
          apply NatTrans.ext
          funext V
          exact congrArg (fun e => e.app ((Over.map f).op.obj V))
            (map_one A.action)
        map_mul' := by
          intro g h
          apply NatTrans.ext
          funext V
          exact congrArg (fun e => e.app ((Over.map f).op.obj V))
            (map_mul A.action g h) }
  torsor := by
    intro V p q
    exact A.torsor ((Over.map f).op.obj V) p q

#check S3128ZMod2SheafTorsor
#check S3128ZMod2SheafTorsor.baseChange

end LeanFormal.IUT.XiFPaper.S3128SheafTorsorActual