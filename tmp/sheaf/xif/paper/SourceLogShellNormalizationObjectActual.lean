import tmp.sheaf.xif.paper.S150SourceLogVolumeNormalizationActual
import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum

/-! # Object: actual source log-shell normalization and the O-boundary gap

This file constructs the actual source log-shell normalization object from the
genuine SourceLogShellDatum, its actual log-shell scale, and the proved
integralLogShell equality.  It also records the object-level gap to a paper
O-boundary log-volume: the formal K x Z boundary log has no canonical logPi and
no actual Haar/nonunit normalization; only the O-times unit log is actual.

No inequality target is touched.

No fake field log/Haar/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.SourceLogShellNormalizationObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S63OBoundaryLogShellActual
open LeanFormal.IUT.XiFPaper.S87OBoundaryDecompositionActual
open LeanFormal.IUT.XiFPaper.S111FormalBoundaryLogActual
open LeanFormal.IUT.XiFPaper.S142NormalizedBoundaryLogVolumeActual
open LeanFormal.IUT.XiFPaper.S150SourceLogVolumeNormalizationActual

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

/-- Actual source log-shell normalization object: genuine source datum, actual
log-shell scale, and the proved integralLogShell identification. -/
structure SourceLogShellNormalizationObject where
  datum : SourceLogShellDatum.{u}
  scale : CommonPrimeCompletion place
  scale_eq : scale = sourceLogVolumeScale place

/-- Actual source log-shell normalization object. -/
noncomputable def sourceLogShellNormalizationObject :
    SourceLogShellNormalizationObject place where
  datum := sourceLocalLogShellDatum (p := p) place
  scale := sourceLogVolumeScale place
  scale_eq := rfl

/-- Normalized O-times log from the actual source datum: scale^{-1} * unitLog. -/
noncomputable def normalizedOTimesLog
    (u : (Integers (CommonPrimeCompletion place))ˣ) :
    CommonPrimeCompletion place :=
  (logShellScale p : CommonPrimeCompletion place)⁻¹ *
    sourceLogShellLog (K := K) (p := p) place u

/-- The object-level gap from the actual O-times log-shell normalization to a
full O-boundary paper log-volume. -/
structure OBoundaryLogVolumeObjectGap where
  carrier : Type u
  carrier_eq : carrier = sourceOBoundaryMonoid (K := K) (p := p) place
  formalLog : sourceOBoundaryMonoid (K := K) (p := p) place →
    CommonPrimeCompletion place × ℤ
  formalLog_eq : formalLog = boundaryLogFormal (K := K) (p := p) place
  canonicalLogPi : Prop
  nonunitHaarNormalization : Prop
  rootThetaNormalization : Prop

/-- Actual object-level gap record.  The Props record what is missing; they are
not asserted. -/
noncomputable def oBoundaryLogVolumeObjectGap :
    OBoundaryLogVolumeObjectGap (K := K) (p := p) place where
  carrier := sourceOBoundaryMonoid (K := K) (p := p) place
  carrier_eq := rfl
  formalLog := boundaryLogFormal (K := K) (p := p) place
  formalLog_eq := rfl
  canonicalLogPi := False
  nonunitHaarNormalization := False
  rootThetaNormalization := False

end LeanFormal.IUT.XiFPaper.SourceLogShellNormalizationObjectActual

end
