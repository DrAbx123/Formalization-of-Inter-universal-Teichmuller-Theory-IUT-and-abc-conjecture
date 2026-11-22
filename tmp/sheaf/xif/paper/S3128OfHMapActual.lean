import tmp.sheaf.xif.paper.S3128BaseChangeOfHActual
import tmp.sheaf.xif.paper.S3128FiberTypeActual
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Iut
open LeanFormal.IUT.XiFPaper.S3128FiberTypeActual
namespace LeanFormal.IUT.XiFPaper.S3128OfHMapActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F}
variable {U : SchemeOverField F} (H : Over U ⥤ Over U)
variable (hH : ∀ V : (Over U)ᵒᵖ, H.op.obj V ≅ V)

abbrev S3128L (V : (Over U)ᵒᵖ) :
    LocallyDiscrete (SchemeOverField F)ᵒᵖ :=
  LocallyDiscrete.mk (Opposite.op V.unop.left)

noncomputable def S3128OfHHMap (V : (Over U)ᵒᵖ) :
    S3128FiberType (X := X) (S3128L (H.op.obj V)) ⥤
      S3128FiberType (X := X) (S3128L V) := by
  let eOver : (H.op.obj V).unop ≅ V.unop :=
    (hH V).unop.symm
  let e : (H.op.obj V).unop.left ≅ V.unop.left :=
    (Over.forget U).mapIso eOver
  let F := X.stack.fiber.map (Discrete.mk e.inv.op)
  exact F.toFunctor

#check S3128OfHHMap
end LeanFormal.IUT.XiFPaper.S3128OfHMapActual