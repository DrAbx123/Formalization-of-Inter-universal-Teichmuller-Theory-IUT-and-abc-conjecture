import Mathlib.AlgebraicGeometry.Sites.Proetale
open AlgebraicGeometry CategoryTheory
#check etaleTopology_le_proetaleTopology
#check proetaleTopology_le_fpqcTopology
#check (inferInstance : proetaleTopology.Subcanonical)
#check (inferInstance : fpqcTopology.Subcanonical)