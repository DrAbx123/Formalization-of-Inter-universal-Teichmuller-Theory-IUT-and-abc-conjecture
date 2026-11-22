import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
noncomputable section
open AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper._ProbeImmActual
variable {X : Scheme} (I : X.IdealSheafData)
example : IsClosedImmersion I.subschemeι := inferInstance
#check IsClosedImmersion.of_isPreimmersion
#check Scheme.IdealSheafData.range_subschemeι
#check Scheme.IdealSheafData.support
end LeanFormal.IUT.XiFPaper._ProbeImmActual
end
