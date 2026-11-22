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

/-- Model hull Haar has the actual unit-reference mass one on the integral log-shell. -/
theorem s3135_modelHullHaar_integralLogShell_eq_one :
    S3135ModelHullHaar
        ((integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime)) :
          Set S3135ModelHullPoint) = 1 :=
  sourceHullHaar_integralLogShell_eq_one

/-- Model hull Haar is finite on the integral log-shell. -/
theorem s3135_modelHullHaar_integralLogShell_lt_top :
    S3135ModelHullHaar
        ((integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime)) :
          Set S3135ModelHullPoint) < ⊤ :=
  haveI : Measure.IsAddHaarMeasure S3135ModelHullHaar := sourceHullHaar_isAddHaar
  (isCompact_integralLogShell (K := concreteLogShellField)
    (p := concreteRationalPrime)).measure_lt_top

#check s3135_modelHullHaar_integralLogShell_eq_one
#check s3135_modelHullHaar_integralLogShell_lt_top
end LeanFormal.IUT.XiFPaper.S3135ModelBatch2Actual