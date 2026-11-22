import tmp.sheaf.xif.paper.S3135HaarNormalizationActual

/-!
# task-52 batch: the paper normalized-Haar equality for the actual unit region

**COMPONENT, not a paper object.**  Consumer: F4 (b) `S3135ScalingLogDegreeZero`.

Applies the task-50 reduction to hull's actual unit region `sourceHullUnitRegion`:
if the paper scaling satisfies the additive modulus law (with modulus `k`), preserves
the actual integral log-shell, and the unit region is measurable, then
`sourceHullHaar ((fun x => c * x) '' sourceHullUnitRegion) = sourceHullHaar
sourceHullUnitRegion`
— the paper `mu(lambda·O) = mu(O)` procession normalization on the actual objects.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual
open LeanFormal.IUT.XiFPaper.S3135HaarModulusActual
open LeanFormal.IUT.XiFPaper.S3135HaarNormalizationActual

namespace LeanFormal.IUT.XiFPaper.S3135HaarNormalizedRegionActual

local instance measCSF3 : MeasurableSpace concreteLogShellField := borel _
local instance borelCSF3 : BorelSpace concreteLogShellField := ⟨rfl⟩

/-- The paper normalized-Haar equality for the actual unit region, from the modulus
law (with unit-scaling forcing) and log-shell self-similarity. -/
theorem s3135_haar_normalized_unitRegion
    (k : concreteLogShellField → ℝ) (hk : ∀ c, 0 ≤ k c)
    (hlaw : ∀ (c : concreteLogShellField), c ≠ 0 → ∀ S : Set concreteLogShellField,
      MeasurableSet S →
        sourceHullHaar ((fun x => c * x) '' S) =
          ENNReal.ofReal (k c) * sourceHullHaar S)
    (c : concreteLogShellField) (hc : c ≠ 0)
    (hU : (fun x => c * x) '' ((integralLogShell (K := concreteLogShellField)
      (p := concreteRationalPrime)) : Set concreteLogShellField) =
      ((integralLogShell (K := concreteLogShellField)
        (p := concreteRationalPrime)) : Set concreteLogShellField))
    (hmeasU : MeasurableSet ((integralLogShell (K := concreteLogShellField)
      (p := concreteRationalPrime)) : Set concreteLogShellField))
    (hmeasO : MeasurableSet (sourceHullUnitRegion : Set concreteLogShellField)) :
    sourceHullHaar ((fun x => c * x) '' (sourceHullUnitRegion : Set concreteLogShellField)) =
      sourceHullHaar (sourceHullUnitRegion : Set concreteLogShellField) := by
  rw [hlaw c hc _ hmeasO,
    s3135_haar_modulus_eq_one_of_unitScaling k hk hlaw c hc hU hmeasU,
    ENNReal.ofReal_one, one_mul]

#check s3135_haar_normalized_unitRegion

end LeanFormal.IUT.XiFPaper.S3135HaarNormalizedRegionActual
end
