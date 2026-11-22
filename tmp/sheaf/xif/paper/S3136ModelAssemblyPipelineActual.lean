import tmp.sheaf.xif.paper.S3136ModelNativeDataWithHaarActual
import tmp.sheaf.xif.paper.S3136ClassARegionVolumeBoundToolActual
import tmp.sheaf.xif.paper.S3136ModelThetaTensorVolumeFiniteActual

/-! # Stage-4 host: model assembly pipeline (missing data -> native datum + Haar -> bounds)

Source anchors: IUT I, Definition 3.1; IUT III, Prop 3.2, (ii); IUT III, Prop 3.9,
(i); IUT IV, Theorem 1.10 shaped estimate.

CONSUMER: hull/qpilot/mainline pipeline. This file states the end-to-end
composition of the model-side data flow:
  LGPModelSourceClauseMissing (hull's exact missing data)
  -> SourceNativeInitialThetaData (native datum, concrete Gaussian arithmetic)
  -> (T, mu := lgpNativeHaarFamily T) (additive Haar family)
  -> compact tensor regions have finite mu-volume.
Each arrow is an actual proved function/instance; no step asserts a missing
estimate (the (c) inequality stays class B; see
S3136RegionEstimateSourceClassificationActual).

LABEL: pipeline component. Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136ModelAssemblyPipelineActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual
open LeanFormal.IUT.XiFPaper.S3136ModelNativeDataWithHaarActual
open LeanFormal.IUT.XiFPaper.S3136ClassARegionVolumeBoundToolActual
open LeanFormal.IUT.XiFPaper.S3136ModelThetaTensorVolumeFiniteActual
open MeasureTheory

variable {l : PrimeGeFive}

/-- Step 1: the exact missing clause data yields the native initial-Theta datum. -/
def lgpModelPipeline_datum (M : LGPModelSourceClauseMissing l) :
    SourceNativeInitialThetaData.{0} l :=
  lgpModelNativeData M

/-- Step 2: the datum carries the concrete Gaussian arithmetic. -/
theorem lgpModelPipeline_datum_arithmetic (M : LGPModelSourceClauseMissing l) :
    (lgpModelPipeline_datum M).arithmetic =
      concreteGaussianInitialThetaArithmeticData l :=
  lgpModelNativeData_arithmetic M

/-- Step 3: the datum together with its concrete additive Haar family. -/
def lgpModelPipeline_datumWithHaar (M : LGPModelSourceClauseMissing l) :
    LGPModelNativeDataWithHaar l :=
  lgpModelNativeDataWithHaar M

/-- Step 4: compact tensor regions have finite native Haar volume. -/
theorem lgpModelPipeline_compact_volume_lt_top
    (M : LGPModelSourceClauseMissing l)
    (b : Bad (nativePlaceSelection (lgpModelPipeline_datum M)))
    {S : Set (qVFamTensorBlock (lgpModelPipeline_datum M) b)}
    (hS : IsCompact S) :
    lgpNativeHaarFamily (lgpModelPipeline_datum M) b S < ⊤ :=
  lgpNativeHaarFamily_measure_lt_top_of_isCompact (lgpModelPipeline_datum M) b hS

#check lgpModelPipeline_datum
#check lgpModelPipeline_datum_arithmetic
#check lgpModelPipeline_datumWithHaar
#check lgpModelPipeline_compact_volume_lt_top

end LeanFormal.IUT.XiFPaper.S3136ModelAssemblyPipelineActual
end