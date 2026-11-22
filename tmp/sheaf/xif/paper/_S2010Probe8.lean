
import Mathlib.AlgebraicGeometry.Limits
open CategoryTheory
open AlgebraicGeometry
namespace Probe
example (T : Scheme.{0}) : Scheme.{0} := T ⨿ T
example (T : Scheme.{0}) : (T ⨿ T) ⟶ T := Limits.coprod.desc (𝟙 T) (𝟙 T)
end Probe
