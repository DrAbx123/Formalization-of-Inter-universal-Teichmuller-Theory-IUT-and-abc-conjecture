import tmp.sheaf.xif.paper.S148QuotientLogVolumeSourceActual
import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum

/-! # S150: source log-volume normalization for the combined formal log-volume

S148 provides combinedLogVolume : (K / unitLogRange) x Z.  This file constructs
the actual source log-volume normalization data:

* the log-shell scale factor (logShellScale p);
* the scaled source integral-unit log map
    sourceLogShellNormalizedMap u = scale^{-1} * unitLog u;
* the corresponding source quotient class;
* the integer formal-logPi coordinate and its relation to the combined volume.

On O-times the unscaled quotient normalized log-volume equals the source
log-shell quotient of unitLog.  The scale factor and the integer formal-logPi
coordinate are separate data; scaling a quotient by a non-unit K factor is not
well-defined on K/unitLogRange without an additional module structure, so that
alignment is recorded as an exact gap, not faked.

No fake field log/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S150SourceLogVolumeNormalizationActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S63OBoundaryLogShellActual
open LeanFormal.IUT.XiFPaper.S87OBoundaryDecompositionActual
open LeanFormal.IUT.XiFPaper.S111FormalBoundaryLogActual
open LeanFormal.IUT.XiFPaper.S126FormalBoundaryLogUseActual
open LeanFormal.IUT.XiFPaper.S143dQuotientLogVolumeActual
open LeanFormal.IUT.XiFPaper.S148QuotientLogVolumeSourceActual

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

/-- Actual log-shell scale factor. -/
noncomputable def sourceLogVolumeScale :
    CommonPrimeCompletion place :=
  (logShellScale p : CommonPrimeCompletion place)

/-- Scaled source integral-unit log map used by the log-shell normalization. -/
noncomputable def sourceLogShellNormalizedMap
    (u : (Integers (CommonPrimeCompletion place))ˣ) :
    CommonPrimeCompletion place :=
  (sourceLogVolumeScale (K := K) (p := p) place)⁻¹ *
    unitLog (K := CommonPrimeCompletion place) u

/-- The source quotient log-volume class of the scaled normalized log. -/
noncomputable def sourceLogShellNormalizedQuotScaled
    (u : (Integers (CommonPrimeCompletion place))ˣ) :
    (CommonPrimeCompletion place) ⧸ unitLogRange (K := K) (p := p) place :=
  QuotientAddGroup.mk' (unitLogRange (K := K) (p := p) place)
    (sourceLogShellNormalizedMap (K := K) (p := p) place u)

/-- Actual source log-volume normalization package. -/
structure SourceLogVolumeNormalization where
  scale : CommonPrimeCompletion place
  scale_eq : scale = sourceLogVolumeScale (K := K) (p := p) place
  normalizedMap : (Integers (CommonPrimeCompletion place))ˣ →
    CommonPrimeCompletion place
  normalizedMap_eq : normalizedMap = sourceLogShellNormalizedMap (K := K) (p := p) place
  quotientMap : (Integers (CommonPrimeCompletion place))ˣ →
    (CommonPrimeCompletion place) ⧸ unitLogRange (K := K) (p := p) place
  quotientMap_eq : quotientMap = sourceLogShellNormalizedQuotScaled (K := K) (p := p) place
  integerAlignment : ∀ x : sourceOBoundaryMonoid (K := K) (p := p) place,
    (combinedLogVolume (K := K) (p := p) place
      (dvrUniformizer (K := K) (p := p) place)
      (dvrUniformizer_irreducible (K := K) (p := p) place) x).2 =
    (boundaryLogFormal (K := K) (p := p) place x).2

/-- Actual source log-volume normalization data. -/
noncomputable def sourceLogVolumeNormalization :
    SourceLogVolumeNormalization (K := K) (p := p) place where
  scale := sourceLogVolumeScale (K := K) (p := p) place
  scale_eq := rfl
  normalizedMap := sourceLogShellNormalizedMap (K := K) (p := p) place
  normalizedMap_eq := rfl
  quotientMap := sourceLogShellNormalizedQuotScaled (K := K) (p := p) place
  quotientMap_eq := rfl
  integerAlignment := by
    intro x
    rfl

/-- On O-times, the unscaled S143d quotient normalized log-volume is the
source log-shell quotient of unitLog. -/
theorem combined_quotient_on_units_eq_source
    (u : (Integers (CommonPrimeCompletion place))ˣ) :
    normalizedLogVolumeQuot (K := K) (p := p) place
        (dvrUniformizer (K := K) (p := p) place)
        (dvrUniformizer_irreducible (K := K) (p := p) place)
        (sourceOTimesToBoundary (K := K) (p := p) place u) =
      sourceLogShellNormalizedQuot (K := K) (p := p) place u :=
  normalizedLogVolumeQuot_on_units_eq_source (K := K) (p := p) place u

/-- The integer formal-logPi coordinate of the combined log-volume is exactly
the second coordinate of boundaryLogFormal; it is not produced by the log-shell
scale. -/
theorem combined_integer_coordinate_alignment
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    (combinedLogVolume (K := K) (p := p) place
        (dvrUniformizer (K := K) (p := p) place)
        (dvrUniformizer_irreducible (K := K) (p := p) place) x).2 =
      (boundaryLogFormal (K := K) (p := p) place x).2 :=
  (sourceLogVolumeNormalization (K := K) (p := p) place).integerAlignment x

end LeanFormal.IUT.XiFPaper.S150SourceLogVolumeNormalizationActual

end
