import tmp.sheaf.xif.paper.S3136NativeHaarFamilyActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual

/-! # Stage-4 host: parameterized unit-region interface candidate (for abc)

Source anchors: IUT III, Prop. 3.2, (ii) (tensor packets of local log-shells);
IUT III, Proposition 3.9, (i) (normalized log-volumes); IUT IV, Theorem 1.10 shape
(undilated region/log-volume estimate).

CONSUMER: abc's parameterized unit-region interface. This file gives the concrete
interface SHAPE over the native mod-side data: a region family on the native one-factor
tensor block, its native additive-Haar volume, and the definitional volume formula.
The unit-region scaling identity and the regionVolume <= normalizedWeight comparison
are NOT proved here: they belong to the analytic/IUT-side estimate (see
S3136RegionEstimateSourceClassificationActual: classB steps).

LABEL: interface shape + explicit missing rows. Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136UnitRegionInterfaceCandidateActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)

/-- A parameterized unit-region interface on the native tensor-block completions: region
family, its native additive-Haar volume, and the definitional formula. -/
structure LGPUnitRegionInterface where
  region : (b : Bad (nativePlaceSelection T)) → Set (qVFamTensorBlock T b)
  volume : (b : Bad (nativePlaceSelection T)) → ℝ≥0∞
  volume_eq : ∀ b, volume b = lgpNativeHaarFamily T b (region b)

/-- The concrete candidate interface for any chosen region family. -/
def lgpUnitRegionInterfaceCandidate
    (region : (b : Bad (nativePlaceSelection T)) → Set (qVFamTensorBlock T b)) :
    LGPUnitRegionInterface T where
  region := region
  volume := fun b => lgpNativeHaarFamily T b (region b)
  volume_eq := fun _ => rfl

/-- The candidate volume is the native Haar volume of the region (restated). -/
theorem lgpUnitRegionInterfaceCandidate_volume
    (region : (b : Bad (nativePlaceSelection T)) → Set (qVFamTensorBlock T b))
    (b : Bad (nativePlaceSelection T)) :
    (lgpUnitRegionInterfaceCandidate T region).volume b = lgpNativeHaarFamily T b (region b) :=
  rfl

/-- The exact missing rows for the unit-region interface (data). -/
def lgpUnitRegionRemaining : List (String × String) :=
  [ ("unit-region scaling identity", "mu(2*O) = mu(O): needs the actual scaled-region comparison of the native Haar family"),
    ("regionVolume <= normalizedWeight", "classB analytic/IUT-side estimate (IUT IV Theorem 1.10 shape; see S3136RegionEstimateSourceClassificationActual)"),
    ("base unit selection", "baseUnit = 2 and the scaling wrapper (abc stream)") ]

theorem lgpUnitRegionRemaining_length : lgpUnitRegionRemaining.length = 3 := rfl

#check LGPUnitRegionInterface
#check lgpUnitRegionInterfaceCandidate
#check lgpUnitRegionInterfaceCandidate_volume
#check lgpUnitRegionRemaining_length

end LeanFormal.IUT.XiFPaper.S3136UnitRegionInterfaceCandidateActual
end