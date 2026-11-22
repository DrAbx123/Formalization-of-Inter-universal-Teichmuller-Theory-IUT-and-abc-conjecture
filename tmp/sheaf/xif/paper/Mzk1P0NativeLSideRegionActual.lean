/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0NativeLSideActual
import tmp.sheaf.xif.paper.Mzk1P0NativeTensorConsumerActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeLSideRegionActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeLSideActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeTensorConsumerActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
theorem nativeLSideRegion_compact : IsCompact (nativeLSideRegion T b) :=
  nativeTensorRegion_compact (p := qVFamTensorP T b) (qVFamTensorPlaces T b) (qVFamTensorTuple)
theorem nativeLSideRegion_measure_lt_top :
    nativeTensorHaar (p := qVFamTensorP T b) (qVFamTensorPlaces T b) (qVFamTensorTuple)
      (nativeLSideRegion T b) < ⊤ :=
  (nativeLSideRegion_compact T b).measure_lt_top
def rows : List String := ["compactness proved from nativeTensorRegion_compact", "finite Haar measure proved"]
theorem rows_length : rows.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeLSideRegionActual
end
