import tmp.sheaf.xif.paper.S1512ProductHaarScalingActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual

namespace Probe2

set_option pp.all true in
#check (inferInstance : NormedField (Completion (Classical.arbitrary (NumberField.FinitePlace ℚ))))
set_option pp.all true in
#check (inferInstance : TopologicalSpace (Completion (Classical.arbitrary (NumberField.FinitePlace ℚ))))
set_option pp.all true in
#check (inferInstance : LocallyCompactSpace (Completion (Classical.arbitrary (NumberField.FinitePlace ℚ))))
set_option pp.all true in
#check (inferInstance : IsTopologicalAddGroup (Completion (Classical.arbitrary (NumberField.FinitePlace ℚ))))
set_option pp.all true in
#check (inferInstance : ContinuousConstSMul (Completion (Classical.arbitrary (NumberField.FinitePlace ℚ)))ˣ (Completion (Classical.arbitrary (NumberField.FinitePlace ℚ))))
set_option pp.all true in
#check (inferInstance : DistribMulAction (Completion (Classical.arbitrary (NumberField.FinitePlace ℚ)))ˣ (Completion (Classical.arbitrary (NumberField.FinitePlace ℚ))))

end Probe2
