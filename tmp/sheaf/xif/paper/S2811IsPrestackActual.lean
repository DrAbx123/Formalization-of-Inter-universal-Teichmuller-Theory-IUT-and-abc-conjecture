import Iut.Foundations.Orbicurve
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.CategoryTheory.Sites.Limits

noncomputable section
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2811IsPrestackActual

universe u

variable (F : Type u) [Field F]

/-- The big etale topology on schemes is subcanonical, via etale ≤ proetale ≤ fpqc. -/
instance schemeEtaleTopologySubcanonical :
    AlgebraicGeometry.Scheme.etaleTopology.Subcanonical :=
  GrothendieckTopology.Subcanonical.of_le
    AlgebraicGeometry.Scheme.etaleTopology_le_proetaleTopology

/-- The over-topology on `SchemeOverField F` is subcanonical. -/
instance schemeOverFieldEtaleTopologySubcanonical :
    (Iut.SchemeOverField.etaleTopology F).Subcanonical := by
  unfold Iut.SchemeOverField.etaleTopology
  infer_instance

#check schemeEtaleTopologySubcanonical
#check schemeOverFieldEtaleTopologySubcanonical
#check GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable


/-- Representable presheaves on `SchemeOverField F` are etale sheaves. -/
theorem S2811_yoneda_isSheaf (S : Iut.SchemeOverField F) :
    Presheaf.IsSheaf (Iut.SchemeOverField.etaleTopology F) (yoneda.obj S) := by
  rw [isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

#check S2811_yoneda_isSheaf
#print axioms S2811_yoneda_isSheaf

end LeanFormal.IUT.XiFPaper.S2811IsPrestackActual
end
