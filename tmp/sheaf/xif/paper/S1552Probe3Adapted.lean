import tmp.sheaf.xif.paper.S1512ProductHaarScalingActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual

namespace Probe3

variable (P : NumberField.FinitePlace ℚ)

#check (inferInstance : NormedField (Completion P))
#check (inferInstance : TopologicalSpace (Completion P))
#check (inferInstance : LocallyCompactSpace (Completion P))
#check (inferInstance : IsTopologicalAddGroup (Completion P))
#check (inferInstance : ContinuousConstSMul (Completion P)ˣ (Completion P))
#check (inferInstance : DistribMulAction (Completion P)ˣ (Completion P))
#check (inferInstance : NormedSpace ℚ_[(completionRationalPrime P).val] (NormalizedCompletion P))
#check (inferInstance : FiniteDimensional ℚ_[(completionRationalPrime P).val] (NormalizedCompletion P))
#check (inferInstance : Algebra ℚ_[(completionRationalPrime P).val] (NormalizedCompletion P))

end Probe3
