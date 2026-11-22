import tmp.sheaf.xif.paper.S3128PullbackCoproductActual
import Mathlib.AlgebraicGeometry.LimitsOver
import Mathlib.AlgebraicGeometry.Limits
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Iut
namespace LeanFormal.IUT.XiFPaper.S3129ProbeCoprod
variable {F : Type} [Field F]
example : HasFiniteCoproducts (SchemeOverField F) := inferInstance
end LeanFormal.IUT.XiFPaper.S3129ProbeCoprod
end