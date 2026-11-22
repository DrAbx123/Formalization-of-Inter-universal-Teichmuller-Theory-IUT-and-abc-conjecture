import tmp.sheaf.xif.paper.S1512ProductHaarScalingActual

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual
open LeanFormal.IUT.NumberFieldFinitePlace

namespace Probe

variable (s : Finset (NumberField.FinitePlace ℚ)) (v : {v // v ∈ s})

#check S1402DependentE s v
#check (inferInstance : NormedField (S1402DependentE s v))
#check (inferInstance : NormedAddCommGroup (S1402DependentE s v))
#check (inferInstance : TopologicalSpace (S1402DependentE s v))
#check (inferInstance : IsTopologicalAddGroup (S1402DependentE s v))
#check (inferInstance : LocallyCompactSpace (S1402DependentE s v))
#check (inferInstance : MeasurableSpace (S1402DependentE s v))
#check (inferInstance : BorelSpace (S1402DependentE s v))
#check (inferInstance : MeasurableSpace (Completion v.1))
#check (inferInstance : BorelSpace (Completion v.1))
#check (inferInstance : NormedField (Completion v.1))
#check (inferInstance : NormedAddCommGroup (Completion v.1))
#check (inferInstance : TopologicalSpace (Completion v.1))
#check (inferInstance : IsTopologicalAddGroup (Completion v.1))
#check (inferInstance : LocallyCompactSpace (Completion v.1))
#check (inferInstance : NormedSpace ℚ_[(completionRationalPrime v.1).val] (Completion v.1))
#check (inferInstance : FiniteDimensional ℚ_[(completionRationalPrime v.1).val] (Completion v.1))
#check (inferInstance : Module.Finite ℚ_[(completionRationalPrime v.1).val] (Completion v.1))
#check (inferInstance : Algebra ℚ_[(completionRationalPrime v.1).val] (Completion v.1))
#check (inferInstance : DistribMulAction (Completion v.1)ˣ (Completion v.1))
#check (inferInstance : ContinuousConstSMul (Completion v.1)ˣ (Completion v.1))
#check (inferInstance : MeasureTheory.Measure.IsAddHaarMeasure (Measure.addHaar : Measure (Completion v.1)))

end Probe
