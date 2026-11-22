import tmp.sheaf.xif.paper.S3128CoproductBaseChangeActual
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.MorphismProperty
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S3128ZMod2FiberCategoryActual
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.S3128OverForgetPreservesActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F}
variable {U U' : SchemeOverField F} (f : U' ⟶ U)
variable (A : S3128ZMod2FiberObj (F := F) X U)

/-- `Over.forget (Spec F)` preserves the specific pullback cospan `A.proj, f`. -/
noncomputable instance S3128OverForgetPreservesPullback
    (g : U' ⟶ U) :
    PreservesLimit (cospan f g)
      (Over.forget (Spec (CommRingCat.of F))) :=
  inferInstance

/-- `Over.forget (Spec F)` preserves all colimits (left adjoint). -/
noncomputable instance S3128OverForgetPreservesColimits :
    PreservesColimits (Over.forget (Spec (CommRingCat.of F))) :=
  inferInstance

/-- Underlying-scheme pullback comparison. -/
noncomputable def S3128UnderlyingPullbackIso :
    (Over.forget (Spec (CommRingCat.of F))).obj (pullback A.proj f) ≅
      pullback (Over.Hom.left A.proj) (Over.Hom.left f) :=
  PreservesPullback.iso
    (Over.forget (Spec (CommRingCat.of F))) A.proj f

#check S3128OverForgetPreservesPullback
#check S3128OverForgetPreservesColimits
#check S3128UnderlyingPullbackIso
#print axioms S3128UnderlyingPullbackIso

end LeanFormal.IUT.XiFPaper.S3128OverForgetPreservesActual