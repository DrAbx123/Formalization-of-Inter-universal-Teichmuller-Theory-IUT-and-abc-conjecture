import Mathlib.AlgebraicGeometry.Sites.Etale
open CategoryTheory AlgebraicGeometry
namespace ProbeBot
#print AlgebraicGeometry.Scheme.etaleTopology
#check @AlgebraicGeometry.Scheme.etaleTopology
#check MorphismProperty.coverage
#check MorphismProperty.grothendieckTopology
-- check the precoverage of the etale topology
example : (AlgebraicGeometry.Scheme.etaleTopology).toPrecoverage =
    MorphismProperty.precoverage @Etale := rfl
end ProbeBot
