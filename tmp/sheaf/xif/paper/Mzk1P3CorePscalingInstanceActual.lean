import tmp.sheaf.xif.paper.Mzk1P3CoreScalingExplicitActual
noncomputable section
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1P3CorePscalingInstanceActual
/-- A bundled explicit scaling instance: endomorphism + constant + measured law. -/
structure CorePscalingInstance (X : Type*) [MeasurableSpace X] where
  μ : Measure X
  f : X → X
  c : ENNReal
  law : ∀ S : Set X, μ (f '' S) = c * μ S
theorem CorePscalingInstance.apply {X : Type*} [MeasurableSpace X]
    (I : CorePscalingInstance X) (S : Set X) :
    I.μ (I.f '' S) = I.c * I.μ S :=
  I.law S
end LeanFormal.IUT.XiFPaper.Mzk1P3CorePscalingInstanceActual
end