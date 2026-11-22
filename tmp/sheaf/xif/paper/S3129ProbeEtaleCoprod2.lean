import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Limits
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper.S3129ProbeEtaleCoprod2
example : IsZariskiLocalAtSource @Etale := inferInstance
example : IsZariskiLocalAtTarget @Etale := inferInstance
end LeanFormal.IUT.XiFPaper.S3129ProbeEtaleCoprod2
end