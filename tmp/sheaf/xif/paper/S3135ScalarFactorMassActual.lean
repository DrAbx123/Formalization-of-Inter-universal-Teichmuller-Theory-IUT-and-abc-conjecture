import tmp.sheaf.xif.paper.S3135HaarUniquenessToolActual

/-!
# task-66: scalar factor of the actual Haar readout — preimage-mass form

**COMPONENT, not a paper object.**  Consumer: F4 (b1) `S3135LogShellScalingIndex`.

From the now-proved scalar step (`S3135HaarUniquenessToolActual`,
`Application.s3135_haarUniquenessScalarStep_proved`), the actual Haar measure of the
preimage of a measurable set under a nonzero scaling is the scalar factor times the
original mass:

`exists C : NNReal, (C : ENNReal) * sourceHullHaar S = sourceHullHaar ((c *:)^-1' S)`

for every measurable `S`.  Applied to `S = (c *:) '' I` (with `I` the actual
integral log-shell, where the preimage is `I` again by injectivity), this is the
lattice-mass equation whose index computation `p ^ (-v(c))` is the remaining datum
`S3135LogShellScalingIndex`; combined with
`S3135HaarIndexActual.s3135_sourceHullHaar_integralLogShell_index` it pins the scalar
to the normalized norm `||c||`.
-/

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Measure
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual
open LeanFormal.IUT.XiFPaper.S3135HaarPushforwardActual
open LeanFormal.IUT.XiFPaper.S3135HaarUniquenessToolActual

namespace LeanFormal.IUT.XiFPaper.S3135ScalarFactorMassActual

local instance measCSF11 : MeasurableSpace concreteLogShellField := borel _
local instance borelCSF11 : BorelSpace concreteLogShellField := ⟨rfl⟩

/-- **Preimage-mass form of the scalar factor**: for a nonzero scaling and a
measurable set, the actual Haar mass of the preimage is the scalar factor times the
original mass. -/
theorem s3135_scalarFactor_measure_preimage
    (c : concreteLogShellField) (hc : c ≠ 0)
    (S : Set concreteLogShellField) (hS : MeasurableSet S) :
    ∃ C : ENNReal,
      C * sourceHullHaar S = sourceHullHaar ((fun x => c * x) ⁻¹' S) := by
  obtain ⟨C, hC⟩ := Application.s3135_haarUniquenessScalarStep_proved c hc
  refine ⟨C, ?_⟩
  rw [← Measure.map_apply (f := fun x => c * x) (s := S)
    (continuous_const.mul continuous_id).measurable hS, hC]
  simp [Measure.smul_apply, smul_eq_mul]

#check s3135_scalarFactor_measure_preimage

end LeanFormal.IUT.XiFPaper.S3135ScalarFactorMassActual
end
