import tmp.sheaf.xif.paper.Mzk1G1AllCompactActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveProjActual
import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1CompactnessInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveProjActual
/-- G1 compactness interface: the all-compact Belyi uniform-ε theorem together
with compactness of the projective Fermat base point. -/
structure G1CompactnessInterface : Prop where
  uniform : UniformEpsilonCriterionRatAll belyiAllCompactSequence
  compact_base : IsCompact ({projFermatBase} : Set (Fin 3 → ℚ))
theorem g1CompactnessInterface_actual : G1CompactnessInterface where
  uniform := belyiAllCompactSequence_uniformEpsilon
  compact_base := Set.finite_singleton _ |>.isCompact
#print axioms g1CompactnessInterface_actual
end LeanFormal.IUT.XiFPaper.Mzk1G1CompactnessInterfaceActual
end