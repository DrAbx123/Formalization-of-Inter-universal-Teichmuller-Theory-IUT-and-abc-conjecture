import tmp.sheaf.xif.paper.S3133QPilotOneColumnRegionCarrierActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.S3131QCActualReadout
import tmp.sheaf.xif.paper.NativeQVPilotNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.S3133QPilotLogVolumeSignActual

/-!
# Actual 1,circ U_Q region object and the field-level missing reading

Source: IUT III, p. 17-18 (iut3.txt 950-1013) and Step (xi), p. 182-183
(iut3.txt 11017-11034): after formation of the hull, the q-pilot object is
compared by applying the normalized log-volume to the region 1,circ U and to the
region that arises from the representation of the q-pilot object at (1,0) on
1,circ U_Q; the log-volume of the latter region is -|log q|.

This file packages the actual partial object of
S3133QPilotOneColumnRegionCarrierActual (region, compactness, actual Haar
measure, actual Q_p-dimension, packet normalization, p-scaled region) as a
single actual structure, aligns it without editing their files with

* the lattice theta-side container S3137QThetaPilotLogVolumeReadingsActual
  (thetaPilotHull is the same actual tensor region);
* the mainline Batch A scalar S3131QC via a named hypothesis;

and records, field-level and with source page/line, the still Missing
identification of the represented region's reading with the actual q-pilot
magnitude |log q|.  No arbitrary field is used and the missing structure is not
inhabited.  No sorry, no axiom, no toy carrier.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option synthInstance.maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3133QPilotOneColumnRegionActualPackaged

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3133QPilotOneColumnRegionCarrierActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3131QCActualReadout
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual
open MeasureTheory

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance qPilotRegionStrucMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance qPilotRegionStrucBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- The actual q-pilot 1,circ U_Q region datum: every field is an actual
construction of the C3 log-shell tensor packet (region, measure, dimension,
normalization, scaled region); the scale law is the actual Proposition 3.9, (i)
shift. -/
structure QPilotOneColumnRegionActual where
  region : Set (C3LogShellTensorBlock C3)
  region_eq : region = qPilotOneColumnRegion C3
  region_compact : IsCompact region
  haar : Measure (C3LogShellTensorBlock C3)
  haar_eq : haar = qPilotOneColumnHaar C3
  dimension : Nat
  dimension_eq : dimension = qPilotOneColumnDimension C3
  dimension_pos : 0 < dimension
  normalizedLogVolume : Set (C3LogShellTensorBlock C3) → Real
  normalizedLogVolume_eq : normalizedLogVolume = qPilotOneColumnNormalizedLogVolume C3
  scaledRegion : Set (C3LogShellTensorBlock C3)
  scaledRegion_eq : scaledRegion = qPilotOneColumnScaledRegion C3

/-- The actual 1,circ U_Q region object, built from the actual C3 tensor packet. -/
noncomputable def qPilotOneColumnRegionActual :
    QPilotOneColumnRegionActual (C3 := C3) where
  region := qPilotOneColumnRegion C3
  region_eq := rfl
  region_compact := qPilotOneColumnRegion_compact C3
  haar := qPilotOneColumnHaar C3
  haar_eq := rfl
  dimension := qPilotOneColumnDimension C3
  dimension_eq := rfl
  dimension_pos := qPilotOneColumnDimension_pos C3
  normalizedLogVolume := qPilotOneColumnNormalizedLogVolume C3
  normalizedLogVolume_eq := rfl
  scaledRegion := qPilotOneColumnScaledRegion C3
  scaledRegion_eq := rfl

/-- Alignment with the lattice theta-side container: the actual 1,circ U region
is exactly S3137's actual Theta-side hull container on the same C3 input. -/
theorem qPilotOneColumnRegion_eq_thetaPilotHull :
    qPilotOneColumnRegion C3 = thetaPilotHull C3 := by
  rw [thetaPilotHull_eq_region]
  exact qPilotOneColumnRegion_eq C3

/-- The actual q-pilot magnitude |log q| on the native side: the actual
procession-normalized q_v log-magnitude. -/
noncomputable def qPilotTargetMagnitude
    (X : N8NativeInput l) [Fintype (Bad (nativePlaceSelection X.S))] : Real :=
  nativeQVPilotNormalizedLogMagnitude X.S

/-- The target magnitude is positive when V_bad is nonempty. -/
theorem qPilotTargetMagnitude_pos
    (X : N8NativeInput l) [Fintype (Bad (nativePlaceSelection X.S))]
    [Nonempty (Bad (nativePlaceSelection X.S))] :
    0 < qPilotTargetMagnitude X := by
  unfold qPilotTargetMagnitude
  exact LeanFormal.IUT.XiFPaper.S3133QPilotLogVolumeSignActual.nativeNormalizedLogMagnitude_pos X

/-- Alignment with the mainline Batch A scalar S3131QC via a named hypothesis:
if QC is the mainline scalar on the same one-column input, then QC is the signed
q-pilot reading -|log q| of the same actual normalized magnitude. -/
theorem qPilotMainline_alignment
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (QC : Real) (hQC : QC = S3131QC T) :
    QC = -nativeQVPilotNormalizedLogMagnitude T := by
  rw [hQC]
  unfold S3131QC nativeQVPilotNormalizedSignedLogVolume
  rfl

/-- Field-level exact Missing identification of the represented 1,circ U_Q region
with the actual q-pilot reading.  Needed data (IUT III p. 17-18, iut3.txt
950-1013; Remark 3.1.1, (ii)-(iv); Step (xi) p. 182-183, iut3.txt 11017-11034):
(i) the source place comparison V_bad <-> C3.tensorIndex (missing capsule
comparison, cf. PrimeStripLogShellActual); (ii) the identification of the q_v
action on the log-shells with the actual p-scaled region; (iii) the procession
weight normalization 1/N_v; (iv) the reading identification
normalizedLogVolume(represented region) = -|log q|. -/
structure MissingQPilotOneColumnReading
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (X : N8NativeInput l) [Fintype (Bad (nativePlaceSelection X.S))] where
  targetMagnitude : Real
  targetMagnitude_eq : targetMagnitude = qPilotTargetMagnitude X
  placeComparison : Prop
  qActionIdentification : Prop
  weightNormalization : Prop
  readingIdentification : Prop

/-- The existence of the missing represented-region reading identification. -/
def MissingQPilotOneColumnReadingData
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (X : N8NativeInput l) [Fintype (Bad (nativePlaceSelection X.S))] : Prop :=
  Nonempty (MissingQPilotOneColumnReading C3 X)

end LeanFormal.IUT.XiFPaper.S3133QPilotOneColumnRegionActualPackaged
