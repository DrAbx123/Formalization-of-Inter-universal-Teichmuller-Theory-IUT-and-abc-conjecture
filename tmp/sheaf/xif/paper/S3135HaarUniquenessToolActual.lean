import Mathlib.MeasureTheory.Measure.Haar.Unique
import tmp.sheaf.xif.paper.S3135HaarPushforwardActual

/-!
# task-64 GLUE TOOL: additive Haar uniqueness (no regularity instances needed)

**Reusable glue file, not a paper object.**  Mathlib provides the no-regularity
uniqueness lemma directly:
`MeasureTheory.Measure.isAddLeftInvariant_eq_smul`
(additive version of `isMulLeftInvariant_eq_smul`,
`MeasureTheory/Measure/Haar/Unique.lean` ~line 923): for a locally compact
second-countable additive group, any left-invariant measure finite on compacts differs
from an additive Haar measure by the Mathlib scalar, with NO `Regular`/`InnerRegular`
instance needed (in a second-countable space all Haar measures are regular).

`s3135_addHaar_eq_smul`: generic tool, `∃ C : ℝ≥0, mu' = C • mu`.

`s3135_haar_pushforward_eq_smul_actual`: concrete application to hull's actual
`sourceHullHaar` (the pushforward Haar half is `S3135HaarPushforwardActual`).

`s3135_haarUniquenessScalarStep_proved`: closes the F4 (b1) exact missing
`S3135HaarUniquenessScalarStep` (ENNReal-coefficient form).

The only remaining F4 (b1) datum is the index computation
`S3135LogShellScalingIndex` (the scalar factor equals the lattice index / norm).
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

namespace LeanFormal.IUT.XiFPaper.S3135HaarUniquenessToolActual

/-- **GLUE TOOL**: two additive Haar measures on a locally compact second-countable
additive group differ by the Mathlib `addHaarScalarFactor` scalar.  No regularity
instance needed (Mathlib `Measure.isAddLeftInvariant_eq_smul`). -/
theorem s3135_addHaar_eq_smul
    {E : Type*} [AddGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [MeasurableSpace E] [BorelSpace E] [LocallyCompactSpace E]
    [SecondCountableTopology E]
    (mu' mu : Measure E) [Measure.IsAddHaarMeasure mu] [Measure.IsAddHaarMeasure mu'] :
    ∃ C : ℝ≥0, mu' = C • mu :=
  ⟨Measure.addHaarScalarFactor mu' mu,
    Measure.isAddLeftInvariant_eq_smul mu' mu⟩

namespace Application

local instance measCSF10 : MeasurableSpace concreteLogShellField := borel _
local instance borelCSF10 : BorelSpace concreteLogShellField := ⟨rfl⟩

/-- Concrete application: the pushforward of hull's actual Haar measure under a
nonzero scaling is a scalar multiple of the Haar measure. -/
theorem s3135_haar_pushforward_eq_smul_actual
    (c : concreteLogShellField) (hc : c ≠ 0) :
    ∃ C : ℝ≥0,
      sourceHullHaar.map (fun x => c * x) = C • sourceHullHaar := by
  haveI hmap : Measure.IsAddHaarMeasure (sourceHullHaar.map (fun x => c * x)) :=
    s3135_pushforward_isAddHaar c hc
  haveI hsrc : Measure.IsAddHaarMeasure sourceHullHaar := sourceHullHaar_isAddHaar
  exact s3135_addHaar_eq_smul (sourceHullHaar.map (fun x => c * x)) sourceHullHaar

/-- **F4 (b1) pushforward-Haar exact missing CLOSED**: the Haar-uniqueness scalar step
in the ENNReal form recorded by `S3135HaarPushforwardActual`. -/
theorem s3135_haarUniquenessScalarStep_proved :
    S3135HaarUniquenessScalarStep := by
  intro c hc
  obtain ⟨C, hC⟩ := s3135_haar_pushforward_eq_smul_actual c hc
  exact ⟨(C : ENNReal), by simpa using hC⟩

end Application

#check s3135_addHaar_eq_smul
#check Application.s3135_haar_pushforward_eq_smul_actual
#check Application.s3135_haarUniquenessScalarStep_proved

end LeanFormal.IUT.XiFPaper.S3135HaarUniquenessToolActual
end
