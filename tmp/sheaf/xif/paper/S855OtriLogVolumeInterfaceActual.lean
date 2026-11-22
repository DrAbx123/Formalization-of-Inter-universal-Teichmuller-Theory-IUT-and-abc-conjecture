import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import LeanFormal.IUT.IUTII.Kummer.MonoAnalyticLogShellCompactCarrier
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
/-! # S855: interface between the actual log-shell carrier and q/root orders
The current LeanFormal MonoAnalyticLogShellCompactCarrier has an actual logShell
and continuous log map, but NO normalized logVolume/Haar on its carrier.
The external IUTStage1Theorem311 has only logShellFamily transport data, not a
SourceMonoAnalyticLogShell structure.  This file connects the actual stack
q/root divisor orders to the carrier and records logVolume normalization as an
exact field.  No completion/field Haar is used. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S855OtriLogVolumeInterfaceActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.MonoAnalyticLogShellCompactCarrier
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
/-- Actual q/root divisor orders from the S782 finite root stack. -/
noncomputable def stackQDivisorOrder : Real :=
  (stackDivisorSection (l := l) T b (stackQSection (l := l) T b)).toAdd
noncomputable def stackRootDivisorOrder : Real :=
  (stackDivisorSection (l := l) T b (stackRootSection (l := l) T b)).toAdd
theorem stackRootDivisorOrder_eq :
    stackRootDivisorOrder (l := l) T b =
      ((qVFamily T b).order : Real) / (2 * (l.value : Real)) := by
  rfl
theorem stackQDivisorOrder_eq :
    stackQDivisorOrder (l := l) T b = ((qVFamily T b).order : Real) := by
  rfl
/-- Interface between the actual log-shell carrier and the q/root orders.
`logVolume` and its normalization are explicit fields; no Haar on the carrier
is constructed in the tree. -/
structure OtriLogVolumeInterface where
  carrier : MonoAnalyticLogShellCompactCarrier.{0}
  qOrder : Real
  rootOrder : Real
  qOrder_eq : qOrder = ((qVFamily T b).order : Real)
  rootOrder_eq : rootOrder = qOrder / (2 * (l.value : Real))
  logVolume : Real
  logVolume_normalization : Prop
/-- Exact interface requirement. -/
def OtriLogVolumeInterfaceRequired : Prop :=
  Nonempty (OtriLogVolumeInterface T b)
/-- Exact logVolume normalization field. -/
def OtriLogVolumeNormalizationRequired
    (D : OtriLogVolumeInterface T b) : Prop :=
  D.logVolume_normalization
end LeanFormal.IUT.XiFPaper.S855OtriLogVolumeInterfaceActual
