import tmp.sheaf.xif.paper.S3135ModelSkeletonInterfaceActual
open scoped NNReal ENNReal
noncomputable section

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
open LeanFormal.IUT.XiFPaper.S3135ModelSkeletonInterfaceActual
open LeanFormal.IUT.XiFPaper.S3135LogShellScalarSelfSimilarityActual

namespace LeanFormal.IUT.XiFPaper.S3135ModelBatch2Actual
local instance measB2 : MeasurableSpace concreteLogShellField := borel _
local instance borelB2 : BorelSpace concreteLogShellField := ⟨rfl⟩

/-- **Region set equality at the model action**: for a Z_p-unit scalar pair
`z * z' = 1`, the scaled integral log-shell equals the integral log-shell. -/
theorem s3135_modelRegion_set_eq
    (z z' : ℤ_[concreteRationalPrime]) (h : z * z' = 1) :
    (fun x : S3135ModelHullPoint =>
        algebraMap ℚ_[concreteRationalPrime] S3135ModelHullPoint
          (z : ℚ_[concreteRationalPrime]) * x) ''
      ((integralLogShell (K := concreteLogShellField)
        (p := concreteRationalPrime)) : Set S3135ModelHullPoint) =
    ((integralLogShell (K := concreteLogShellField)
      (p := concreteRationalPrime)) : Set S3135ModelHullPoint) :=
  s3135_integralLogShell_scalarUnit_selfSimilarity (K := concreteLogShellField)
    (p := concreteRationalPrime) z z' h

/-- Consequence: the model Haar readout is invariant (μ equality by set equality). -/
theorem s3135_modelHaar_eq_of_region_set_eq
    (z z' : ℤ_[concreteRationalPrime]) (h : z * z' = 1) :
    S3135ModelHullHaar
        ((fun x : S3135ModelHullPoint =>
            algebraMap ℚ_[concreteRationalPrime] S3135ModelHullPoint
              (z : ℚ_[concreteRationalPrime]) * x) ''
          ((integralLogShell (K := concreteLogShellField)
            (p := concreteRationalPrime)) : Set S3135ModelHullPoint)) =
      S3135ModelHullHaar
        ((integralLogShell (K := concreteLogShellField)
          (p := concreteRationalPrime)) : Set S3135ModelHullPoint) := by
  rw [s3135_modelRegion_set_eq z z' h]

#check s3135_modelRegion_set_eq
#check s3135_modelHaar_eq_of_region_set_eq
end LeanFormal.IUT.XiFPaper.S3135ModelBatch2Actual