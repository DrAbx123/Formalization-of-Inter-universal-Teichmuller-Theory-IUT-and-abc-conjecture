import Mathlib.AlgebraicGeometry.Pullbacks
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Iut
namespace LeanFormal.IUT.XiFPaper.S3129ProbeOver
variable {F : Type} [Field F] (S T X : SchemeOverField F) (f : S ⟶ T) (x : X ⟶ T)
#check Over.homMk
#check Over.mk
#check Over.hom_ext
#check Comma.hom_ext
#check Over.w
#check Over.Hom.w
end LeanFormal.IUT.XiFPaper.S3129ProbeOver
end