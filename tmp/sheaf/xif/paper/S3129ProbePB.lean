import tmp.sheaf.xif.paper.S3129GenericRepresentablePullbackActual
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Iut
namespace LeanFormal.IUT.XiFPaper.S3129ProbePB
variable {F : Type} [Field F] (S T X : SchemeOverField F) (f : S ⟶ T) (x : X ⟶ T)
#check IsPullback.of_hasPullback
#check IsPullback.of_hasPullback f x
#check pullbackIsPullback
#check pullbackIsPullback f x
end LeanFormal.IUT.XiFPaper.S3129ProbePB
end