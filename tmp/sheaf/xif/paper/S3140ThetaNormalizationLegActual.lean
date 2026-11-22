import tmp.sheaf.xif.paper.S3134LastSeamExactMissingActual
import tmp.sheaf.xif.paper.S3132ThetaNormalizationFactorActual
import tmp.sheaf.xif.paper.S3132CanonicalRootedThetaTargetActual
import tmp.sheaf.xif.paper.S3132Task30ThetaHalfActual

/-!
# S3140: the normalized Theta leg — raw last-seam equality + hull normalization channel

**Component, not paper object.**  This file composes three actual ingredients into
the hull task-30 minimal exact missing (the Theta half of the fourth-triangle
last-seam identification):

1. shehdd's raw last-seam Theta equality
   `S3134LastSeamThetaMissing`: the negative raw HDD determinant log-volume equals
   the raw Haar log-volume of the C3 hull — rewritten here in hull's naming as
   `c3ThetaRawHaarLogVolume C3`;
2. hull's raw-Haar -> degree-normalized V-form channel
   (`S3132ThetaNormalizationFactorActual`): `thetaPilotHullLogVolumeReal C3 =
   c3NormalizedLogVolume C3 (actual paper hull) + thetaNormalizationFactor C3`;
3. the V-form identification `c3NormalizedLogVolume C3 (actual paper hull) =
   S3134CanonicalRootedHC T mu` and the vanishing of the exact normalization
   factor, which by hull's proved reduction give the sharper canonical target
   `thetaPilotHullLogVolumeReal C3 = S3134CanonicalRootedHC T mu`.

Together with shehdd's named Theta-side identification
`S3134CanonicalRootedHC T mu = S3134Step3115ThetaPilotReadout D`, this yields hull's
`MissingFourthTriangleThetaHalfReadout` and hence the fourth-triangle signed
Step (xi-f) ray (given the R1 same-C residual and the q half).

Dependency order (recorded): RAW last-seam Theta equality + normalization-factor
zero + V-form identification => canonical rooted Theta target => (with the named
raw/canonical identification) task-30 Theta half => ray.  The raw convention does
NOT include the V-form normalization.

No sorry/axiom/arbitrary carrier.  WRITE-ONLY: no lake/lean.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointQThetaActual
open LeanFormal.IUT.XiFPaper.S3134MainlineRootedHFaActual
open LeanFormal.IUT.XiFPaper.S3134Step3115To312Actual
open LeanFormal.IUT.XiFPaper.S3134LastSeamExactMissingActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137NativeToC3SameCReadoutActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3132ThetaNormalizationFactorActual
open LeanFormal.IUT.XiFPaper.S3132CanonicalRootedThetaTargetActual
open LeanFormal.IUT.XiFPaper.S3132Task30ThetaHalfActual
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.S3140ThetaNormalizationLegActual

universe u v uv upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{0, uv, upi, umon, ui} l V)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [forall b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [forall b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]
variable (mu : forall b : Bad (nativePlaceSelection T),
  Measure (qVFamTensorBlock T b))
variable [forall b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]
variable {V0 : Type} {I0 : OriginalInput l V0}
variable (C3 : SourcePilotRegionData (l := l) (V := V0) I0)
variable (P : PaperQPilotObjectActual (l := l) (I := I0))

/-- The raw last-seam Theta equality rewritten in hull's naming: the negative raw
HDD determinant log-volume equals the raw Haar log-volume of the C3 hull. -/
theorem S3140LastSeamThetaMissing_iff_rawHaar
    (D : S1300HDDHullDetSource I) :
    S3134LastSeamThetaMissing (I := I) D C3 ↔
      -(D.detData.logVolume (S3134ThetaHullRegion (I := I) D)).toReal =
        c3ThetaRawHaarLogVolume C3 := by
  unfold S3134LastSeamThetaMissing c3ThetaRawHaarLogVolume thetaPilotHull
  exact Iff.rfl

/-- Hull's sharper canonical rooted Theta target from the normalization channel:
vanishing exact normalization factor + V-form identification give
`thetaPilotHullLogVolumeReal C3 = S3134CanonicalRootedHC T mu`. -/
theorem S3140MissingCanonicalRootedThetaReadout_of_factor_zero
    (hfac : thetaNormalizationFactor C3 = 0)
    (hV : c3NormalizedLogVolume C3
        (actualHolomorphicHull C3 (actualUnitRegion C3)) =
          S3134CanonicalRootedHC (l := l) T mu) :
    MissingCanonicalRootedThetaReadout (I := I) (V0 := V0) (I0 := I0)
      C3 T (mu := mu) :=
  ⟨thetaPilotHullLogVolumeReal_eq_canonical_of_factor_zero (C3 := C3) hfac hV⟩

/-- Hull task-30 minimal exact missing (the Theta half) from the normalized leg:
the canonical target plus shehdd's named Theta-side identification. -/
theorem S3140MissingThetaHalfReadout_of_factor_zero
    (D : S1300HDDHullDetSource I)
    (hfac : thetaNormalizationFactor C3 = 0)
    (hV : c3NormalizedLogVolume C3
        (actualHolomorphicHull C3 (actualUnitRegion C3)) =
          S3134CanonicalRootedHC (l := l) T mu)
    (hH : S3134CanonicalRootedHC (l := l) T mu =
      S3134Step3115ThetaPilotReadout (I := I) D) :
    MissingFourthTriangleThetaHalfReadout (I := I) (I0 := I0) C3 D :=
  ⟨S3134Step3115ThetaPilotReadout_eq_thetaPilot_of_canonical
      (I := I) (T := T) (mu := mu) (C3 := C3) D
      (S3140MissingCanonicalRootedThetaReadout_of_factor_zero
        (I := I) (T := T) (mu := mu) (C3 := C3) hfac hV) hH⟩

/-- Fourth-triangle Step (xi-f) ray from the normalized Theta leg, the R1 same-C
residual and the q-half identification (mirrors hull's task-30 composition). -/
theorem S3140FourthTriangleResidual_of_normalization
    (D : S1300HDDHullDetSource I)
    (B : NativeToC3SameCReadoutIdentification (l := l) T mu C3 P)
    (hfac : thetaNormalizationFactor C3 = 0)
    (hV : c3NormalizedLogVolume C3
        (actualHolomorphicHull C3 (actualUnitRegion C3)) =
          S3134CanonicalRootedHC (l := l) T mu)
    (hH : S3134CanonicalRootedHC (l := l) T mu =
      S3134Step3115ThetaPilotReadout (I := I) D)
    (hq : S3134Step3115QPilotReadout (J := J) = qPilotLogVolumeReading P) :
    S3134Step3115QPilotReadout (J := J) ∈
      hullLogVolumeRay (S3134Step3115ThetaPilotReadout (I := I) D) :=
  S3134FourthTriangleResidual_of_missingThetaHalf
    (I := I) (J := J) (T := T) (mu := mu) (V0 := V0) (I0 := I0)
    (C3 := C3) (P := P) D B
    (S3140MissingThetaHalfReadout_of_factor_zero
      (I := I) (T := T) (mu := mu) C3 D hfac hV hH) hq

#check S3140LastSeamThetaMissing_iff_rawHaar
#check S3140MissingCanonicalRootedThetaReadout_of_factor_zero
#check S3140MissingThetaHalfReadout_of_factor_zero
#check S3140FourthTriangleResidual_of_normalization

end LeanFormal.IUT.XiFPaper.S3140ThetaNormalizationLegActual
