import tmp.sheaf.xif.paper.S1512ProductHaarScalingActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual

namespace Probe4

variable (P : NumberField.FinitePlace ℚ)

#check (inferInstance : ProperSpace (Completion P))
#check (inferInstance : SecondCountableTopology (Completion P))
#check (inferInstance : MeasurableSpace (NormalizedCompletion P))
#check (inferInstance : BorelSpace (NormalizedCompletion P))
#check (inferInstance : Measure.IsAddHaarMeasure (Measure.addHaar : Measure (NormalizedCompletion P)))
#check (inferInstance : Regular (Measure.addHaar : Measure (Completion P)))
#check (inferInstance : Regular (Measure.addHaar : Measure (NormalizedCompletion P)))
#check (inferInstance : IsTopologicalAddGroup (NormalizedCompletion P))
#check (inferInstance : LocallyCompactSpace (NormalizedCompletion P))
#check (inferInstance : TopologicalSpace (NormalizedCompletion P))

end Probe4
