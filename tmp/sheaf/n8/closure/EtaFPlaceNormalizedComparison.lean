import tmp.sheaf.n8.closure.C3TensorTargetCorrection
import tmp.sheaf.n8.closure.C9QPilotRegion
import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogShellVolumeConsumer
import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum

/-!
# Eta F-place normalized comparison

Carrier audit correction: the selected shell must be at the actual native
F-place nativeFPlaceOverBad X, not at the old Fmod selected completion.

Actual data used:
- F-place completion CommonPrimeCompletion (nativeFPlaceAtPrime X);
- production sourceLocalLogShellDatum at that F-place;
- production LogShellVolumeConsumer at the same F-place/prime;
- production selected q normalization qPilotProcessionNormalizedVolume.

The comparison target is between the actual F-shell logVolume
(Real.log of the production volume index) and the production normalized q
volume.  It is an exact gap, not a raw equality of q and volume, and no
arbitrary normalization/quasi-coherent map is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison

open scoped Padic

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open ABCBridge.N8.C3TensorTargetCorrection
open LeanFormal.IUT.Foundations.LocalFields.LogShellVolume
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.NumberFieldFinitePlace

variable {l : PrimeGeFive}
variable {X : N8NativeInput l}

/-- Actual F-place completion at the native F-place. -/
abbrev FPlaceCompletion (X : N8NativeInput l) : Type :=
  CommonPrimeCompletion (nativeFPlaceAtPrime X)

/-- Actual F-place log-shell datum (not the Fmod selected shell). -/
noncomputable def fPlaceShell (X : N8NativeInput l) : SourceLogShellDatum :=
  sourceLocalLogShellDatum (K := X.S.arithmetic.F) (p := nativePrime X)
    (nativeFPlaceAtPrime X)

/-- Actual F-place volume container. -/
noncomputable def fPlaceVolumeConsumer (X : N8NativeInput l) :
    LogShellVolumeConsumer (K := FPlaceCompletion X) (p := nativePrime X) :=
  logShellVolumeConsumer (K := FPlaceCompletion X) (p := nativePrime X)

/-- Actual production volume index at the F-place. -/
def fPlaceVolumeIndex (X : N8NativeInput l) : Nat :=
  (fPlaceVolumeConsumer X).index

/-- Actual F-shell log-volume readout. -/
def fPlaceLogVolume (X : N8NativeInput l) : Real :=
  Real.log (fPlaceVolumeIndex X : Real)

/-- Production selected-place normalized q volume. -/
def fPlaceNormalizedQVolume (X : N8NativeInput l) : Real :=
  qPilotProcessionNormalizedVolume X

/-- Corrected normalized comparison target: F-shell log-volume equals the
production normalized q volume.  This is an exact gap (no proof claimed). -/
def EtaFPlaceNormalizedComparisonTarget (X : N8NativeInput l) : Prop :=
  fPlaceLogVolume X = fPlaceNormalizedQVolume X

/-- Actual F-place normalized readout package: shell, volume index, log-volume
and production normalized q volume. -/
structure EtaFPlaceNormalizedReadout (X : N8NativeInput l) where
  shell : SourceLogShellDatum
  shell_eq : shell = fPlaceShell X
  volumeIndex : Nat
  volumeIndex_eq : volumeIndex = fPlaceVolumeIndex X
  logVolume : Real
  logVolume_eq : logVolume = Real.log (volumeIndex : Real)
  normalizedQVolume : Real
  normalizedQVolume_eq : normalizedQVolume = fPlaceNormalizedQVolume X

/-- Actual F-place readout; all fields are production/canonical values. -/
noncomputable def etaFPlaceNormalizedReadout (X : N8NativeInput l) :
    EtaFPlaceNormalizedReadout X where
  shell := fPlaceShell X
  shell_eq := rfl
  volumeIndex := fPlaceVolumeIndex X
  volumeIndex_eq := rfl
  logVolume := fPlaceLogVolume X
  logVolume_eq := rfl
  normalizedQVolume := fPlaceNormalizedQVolume X
  normalizedQVolume_eq := rfl

theorem fPlaceLogVolume_eq_log_index (X : N8NativeInput l) :
    fPlaceLogVolume X = Real.log (fPlaceVolumeIndex X : Real) :=
  rfl

theorem etaFPlaceNormalizedReadout_shell_eq
    (B : EtaFPlaceNormalizedReadout X) :
    B.shell = fPlaceShell X :=
  B.shell_eq

/-- Exact comparison gap restated through the actual readout package. -/
theorem etaFPlaceNormalizedComparison_iff_readout_gap
    (X : N8NativeInput l) :
    EtaFPlaceNormalizedComparisonTarget X ↔
      (etaFPlaceNormalizedReadout X).logVolume =
        (etaFPlaceNormalizedReadout X).normalizedQVolume :=
  Iff.rfl

end LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
