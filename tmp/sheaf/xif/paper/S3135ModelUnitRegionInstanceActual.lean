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

local instance measB3u : MeasurableSpace concreteLogShellField := borel _
local instance borelB3u : BorelSpace concreteLogShellField := ⟨rfl⟩

/-- **Parameterized model unit-region instance** (unit region = the actual integral
log-shell; hull = the unit region; log-degree identically zero; bound zero).  The
completion scaling point and its base-unit equation are supplied by the model. -/
def s3135_modelUnitRegionData
    {l : PrimeGeFive} {V : Type} (I : OriginalInput l V) (v : V)
    (valueUnit : (I.ValueMonoidAt 0 0 v)ˣ)
    (baseUnit : ℚ_[concreteRationalPrime]ˣ)
    (baseUnit_norm_one : ‖(baseUnit : ℚ_[concreteRationalPrime])‖ = 1)
    (scalingPoint : S3135ModelHullPoint)
    (scalingPoint_eq : scalingPoint =
      algebraMap ℚ_[concreteRationalPrime] S3135ModelHullPoint
        (baseUnit : ℚ_[concreteRationalPrime]) * (1 : S3135ModelHullPoint)) :
    S3135ModelUnitRegionHaarData I v where
  valueUnit := valueUnit
  baseUnit := baseUnit
  baseUnit_norm_one := baseUnit_norm_one
  hull := ((integralLogShell (K := concreteLogShellField)
    (p := concreteRationalPrime)) : Set S3135ModelHullPoint)
  unitRegion := ((integralLogShell (K := concreteLogShellField)
    (p := concreteRationalPrime)) : Set S3135ModelHullPoint)
  unitRegion_eq_logShell := rfl
  modelLogDegree := fun _ => 0
  degreeBound := 0
  hull_subset := fun _ hx => hx
  unitRegion_logDegree_le := fun _ _ => le_refl 0
  scalingPoint := scalingPoint
  scalingPoint_eq := scalingPoint_eq
  scaling_logDegree_nonpos := le_refl 0

/-- The constructed model unit-region data has zero-valued model log-degree on its
unit region. -/
theorem s3135_modelUnitRegionData_logDegree_nonpos
    {l : PrimeGeFive} {V : Type} (I : OriginalInput l V) (v : V)
    (valueUnit : (I.ValueMonoidAt 0 0 v)ˣ)
    (baseUnit : ℚ_[concreteRationalPrime]ˣ)
    (baseUnit_norm_one : ‖(baseUnit : ℚ_[concreteRationalPrime])‖ = 1)
    (scalingPoint : S3135ModelHullPoint)
    (scalingPoint_eq : scalingPoint =
      algebraMap ℚ_[concreteRationalPrime] S3135ModelHullPoint
        (baseUnit : ℚ_[concreteRationalPrime]) * (1 : S3135ModelHullPoint)) :
    (s3135_modelUnitRegionData I v valueUnit baseUnit baseUnit_norm_one
        scalingPoint scalingPoint_eq).modelLogDegree scalingPoint ≤ 0 :=
  le_refl 0

#check s3135_modelUnitRegionData
#check s3135_modelUnitRegionData_logDegree_nonpos
end LeanFormal.IUT.XiFPaper.S3135ModelBatch3Actual