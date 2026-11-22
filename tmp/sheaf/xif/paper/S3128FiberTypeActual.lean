import tmp.sheaf.xif.paper.S3128SheafTorsorActual
import Iut.Foundations.Orbicurve
noncomputable section
open CategoryTheory
open Iut
namespace LeanFormal.IUT.XiFPaper.S3128FiberTypeActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F}

noncomputable def S3128FiberBundle
    (L : LocallyDiscrete (SchemeOverField F)ᵒᵖ) :
    Bundled Category.{0, 0} :=
  (X.stack.fiber.obj L : Bundled Category.{0, 0})

def S3128FiberType
    (L : LocallyDiscrete (SchemeOverField F)ᵒᵖ) : Type _ :=
  (S3128FiberBundle (X := X) L).α

instance S3128FiberTypeCategory
    (L : LocallyDiscrete (SchemeOverField F)ᵒᵖ) :
    Category (S3128FiberType (X := X) L) :=
  (S3128FiberBundle (X := X) L).str

#check S3128FiberType
#check S3128FiberTypeCategory
end LeanFormal.IUT.XiFPaper.S3128FiberTypeActual