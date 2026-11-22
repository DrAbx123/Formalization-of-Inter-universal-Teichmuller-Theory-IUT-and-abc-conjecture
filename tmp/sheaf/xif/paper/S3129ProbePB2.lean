import tmp.sheaf.xif.paper.S3129GenericRepresentablePullbackActual
import Mathlib.AlgebraicGeometry.Pullbacks
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Iut
namespace LeanFormal.IUT.XiFPaper.S3129ProbePB2
variable {F : Type} [Field F] (S T X : SchemeOverField F) (f : S ⟶ T) (x : X ⟶ T)
#check (IsPullback.of_hasPullback f x)
#check Over.forget
#check IsPullback.map
end LeanFormal.IUT.XiFPaper.S3129ProbePB2
end