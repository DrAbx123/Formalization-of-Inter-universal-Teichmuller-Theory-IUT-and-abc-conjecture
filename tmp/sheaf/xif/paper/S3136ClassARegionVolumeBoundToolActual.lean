import tmp.sheaf.xif.paper.S3136ModelThetaTensorVolumeFiniteActual

/-! # Stage-4 host: class-A region-volume bound tools on the native tensor block

Source anchors: IUT III, Prop. 3.2, (ii) (compact tensor log-shell regions with
additive Haar); IUT III, Prop. 3.9, (i) (normalized log-volumes); IUT IV, Theorem
1.10 shaped estimate (class B target, see
S3136RegionEstimateSourceClassificationActual).

CONSUMER: mainline/abc region-volume comparisons. This file supplies the CLASS A
measure-theoretic tools: monotonicity of the native Haar volume in the region, and
the conditional form of the (c) inequality as explicit data (the normalized weight
is supplied by the consumer; the inequality itself is class B and NOT proved).

LABEL: generic tools (class A) + explicit missing estimate data. Registry frozen;
new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136ClassARegionVolumeBoundToolActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Monotonicity of the native Haar volume in the region. -/
theorem lgpNativeHaarFamily_mono {S U : Set (qVFamTensorBlock T b)}
    (hSU : S ⊆ U) :
    lgpNativeHaarFamily T b S ≤ lgpNativeHaarFamily T b U :=
  measure_mono hSU

/-- A region-volume bound in conditional form: region family, normalized weight,
and the exact (c) inequality as data (class B input). -/
structure LGPRegionVolumeBound where
  region : (b : Bad (nativePlaceSelection T)) → Set (qVFamTensorBlock T b)
  normalizedWeight : (b : Bad (nativePlaceSelection T)) → ℝ≥0∞
  regionVolume_le_normalizedWeight :
    ∀ b, lgpNativeHaarFamily T b (region b) ≤ normalizedWeight b

/-- The volume part of the bound is the native Haar volume. -/
theorem LGPRegionVolumeBound.volume_le (B : LGPRegionVolumeBound T) (b : Bad (nativePlaceSelection T)) :
    lgpNativeHaarFamily T b (B.region b) ≤ B.normalizedWeight b :=
  B.regionVolume_le_normalizedWeight b

/-- Compact regions have finite native Haar volume (recorded for the estimate). -/
theorem LGPRegionVolumeBound.volume_lt_top_of_compact
    (B : LGPRegionVolumeBound T) {S : Set (qVFamTensorBlock T b)}
    (hS : IsCompact S) :
    lgpNativeHaarFamily T b S < ⊤ :=
  IsCompact.measure_lt_top hS

#check lgpNativeHaarFamily_mono
#check LGPRegionVolumeBound
#check LGPRegionVolumeBound.volume_le
#check LGPRegionVolumeBound.volume_lt_top_of_compact

end LeanFormal.IUT.XiFPaper.S3136ClassARegionVolumeBoundToolActual
end