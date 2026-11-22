import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Subcanonical

open CategoryTheory AlgebraicGeometry

namespace TestEtale

noncomputable instance etaleSubcanonical : Scheme.etaleTopology.Subcanonical :=
  .of_le (le_trans AlgebraicGeometry.Scheme.etaleTopology_le_proetaleTopology
    AlgebraicGeometry.Scheme.proetaleTopology_le_fpqcTopology)

example : Scheme.etaleTopology.Subcanonical := inferInstance

end TestEtale
