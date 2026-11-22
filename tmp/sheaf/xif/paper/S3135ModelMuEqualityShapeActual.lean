import tmp.sheaf.xif.paper.S3135ModelSkeletonInterfaceActual

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Measure
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual
open LeanFormal.IUT.XiFPaper.S3135LogShellScalarSelfSimilarityActual
open LeanFormal.IUT.XiFPaper.S3135ModelSkeletonInterfaceActual

namespace LeanFormal.IUT.XiFPaper.S3135ModelBatch3Actual

local instance measB3m : MeasurableSpace concreteLogShellField := borel _
local instance borelB3m : BorelSpace concreteLogShellField := ⟨rfl⟩

/-- **Model Haar scaling equality on the unit region** (μ(2·O)=μ(O) shape): for a
Z_p-unit scalar pair z, z' with z * z' = 1, the actual Haar readout of the scaled unit
region equals that of the unit region, where the scaling action is multiplication by
`algebraMap z 1` and the unit region is the actual integral log-shell. -/
theorem s3135_modelHaar_scaling_eq_unitRegion
    (z z' : ℤ_[concreteRationalPrime]) (h : z * z' = 1) :
    S3135ModelHullHaar
        ((fun x : S3135ModelHullPoint =>
            algebraMap ℚ_[concreteRationalPrime] S3135ModelHullPoint
              (z : ℚ_[concreteRationalPrime]) *
              (1 : S3135ModelHullPoint) * x) ''
          ((integralLogShell (K := concreteLogShellField)
            (p := concreteRationalPrime)) : Set S3135ModelHullPoint)) =
      S3135ModelHullHaar
        ((integralLogShell (K := concreteLogShellField)
          (p := concreteRationalPrime)) : Set S3135ModelHullPoint) := by
  have hfun : (fun x : S3135ModelHullPoint =>
        algebraMap ℚ_[concreteRationalPrime] S3135ModelHullPoint
          (z : ℚ_[concreteRationalPrime]) * (1 : S3135ModelHullPoint) * x) =
      (fun x : S3135ModelHullPoint =>
        algebraMap ℚ_[concreteRationalPrime] S3135ModelHullPoint
          (z : ℚ_[concreteRationalPrime]) * x) := by
    funext x
    rw [mul_assoc, one_mul]
  rw [hfun]
  exact S3135ModelHaar_scaling_image_eq z z' h

#check s3135_modelHaar_scaling_eq_unitRegion
end LeanFormal.IUT.XiFPaper.S3135ModelBatch3Actual