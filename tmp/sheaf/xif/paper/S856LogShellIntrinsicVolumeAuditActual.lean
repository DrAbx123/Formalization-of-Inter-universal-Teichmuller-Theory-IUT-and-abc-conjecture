import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier
import LeanFormal.IUT.IUTII.Kummer.MonoAnalyticLogShellFormalLogMul
import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual

/-! # S856: log-shell intrinsic volume vs S782 q/root sections

`SourceLogShellDatum` supplies `preLogShell`, `logShell`, an arbitrary monoid
hom `logMap : Units ->* Multiplicative K`, and the `pStar` scaling.  It has no
intrinsic `logVolume`/Haar field, so `V(q)=order*log p` and
`V(root)=order/(2l)*log p` are not derivable from the carrier alone.
`MonoAnalyticLogShellFormalLogMul` supplies formal log multiplicativity, not a
volume normalized at q/root.  S782 supplies the finite root-stack sections
with real divisor coordinates `order` and `order/(2l)`, but no map into the
log-shell carrier.  This file records the exact minimal spec and the actual
S782 coordinate facts.  No L(mu_2l) field Haar is used.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S856LogShellIntrinsicVolumeAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Exact intrinsic-volume spec on a log-shell carrier.  The carrier has no
volume field; this structure is the minimal data needed to state the two paper
normalizations. -/
structure SourceLogShellIntrinsicVolume
    (D : SourceLogShellDatum.{u}) where
  qUnit : D.Units
  rootUnit : D.Units
  /-- Additive log-volume on the log coordinate field K. -/
  volumeLog : D.K →+ Real
  /-- p-adic normalization of the log-shell factor. -/
  pStar_normalization :
    volumeLog (D.pStar : D.K) = Real.log (D.pStar : Real)
  /-- q-pilot normalization: V(q) = order * log p. -/
  q_normalization :
    volumeLog ((D.logMap qUnit).toAdd) =
      ((qVFamily T b).order : Real) * Real.log (D.p : Real)
  /-- root normalization: V(root) = order/(2l) * log p. -/
  root_normalization :
    volumeLog ((D.logMap rootUnit).toAdd) =
      (((qVFamily T b).order : Real) / (2 * (l.value : Real))) *
        Real.log (D.p : Real)

/-- The exact minimal spec, recorded as a Prop without inhabitant. -/
def SourceLogShellIntrinsicVolumeSpec (D : SourceLogShellDatum.{u}) : Prop :=
  Nonempty (SourceLogShellIntrinsicVolume (l := l) T b D)

/-- S782 q-section has real divisor coordinate exactly order(q_v). -/
theorem stackQSection_divisor_eq_order :
    (stackQSection (l := l) T b).2 =
      Multiplicative.ofAdd ((qVFamily T b).order : Real) := rfl

/-- S782 root-section has real divisor coordinate exactly order(q_v)/(2l). -/
theorem stackRootSection_divisor_eq_order_div :
    (stackRootSection (l := l) T b).2 =
      Multiplicative.ofAdd (((qVFamily T b).order : Real) /
        (2 * (l.value : Real))) := rfl

/-- S782's q/root sections are actual units with the exact 2l-th power law. -/
theorem stackRootSection_pow_twoL_actual :
    stackRootSection (l := l) T b ^ (2 * l.value) = stackQSection (l := l) T b :=
  stackRootSection_pow (l := l) T b

/-- Exact bridge still needed: a map from S782 stack sections into the
log-shell carrier, plus an additive log-volume matching the S782 real
divisor coordinates. -/
structure StackSectionToLogShellVolumeBridge
    (D : SourceLogShellDatum.{u}) where
  qUnit : D.Units
  rootUnit : D.Units
  volumeLog : D.K →+ Real
  q_normalization :
    volumeLog ((D.logMap qUnit).toAdd) =
      ((qVFamily T b).order : Real) * Real.log (D.p : Real)
  root_normalization :
    volumeLog ((D.logMap rootUnit).toAdd) =
      (((qVFamily T b).order : Real) / (2 * (l.value : Real))) *
        Real.log (D.p : Real)

def StackSectionToLogShellVolumeBridgeRequired
    (D : SourceLogShellDatum.{u}) : Prop :=
  Nonempty (StackSectionToLogShellVolumeBridge (l := l) T b D)

/-- Conditional actual q-normalization from the exact stack bridge. -/
theorem volume_q_of_stackBridge
    (D : SourceLogShellDatum.{u})
    (B : StackSectionToLogShellVolumeBridge (l := l) T b D) :
    B.volumeLog ((D.logMap B.qUnit).toAdd) =
      ((qVFamily T b).order : Real) * Real.log (D.p : Real) := by
  exact B.q_normalization

/-- Conditional actual root-normalization from the exact stack bridge. -/
theorem volume_root_of_stackBridge
    (D : SourceLogShellDatum.{u})
    (B : StackSectionToLogShellVolumeBridge (l := l) T b D) :
    B.volumeLog ((D.logMap B.rootUnit).toAdd) =
      (((qVFamily T b).order : Real) / (2 * (l.value : Real))) *
        Real.log (D.p : Real) := by
  exact B.root_normalization

end LeanFormal.IUT.XiFPaper.S856LogShellIntrinsicVolumeAuditActual

end
