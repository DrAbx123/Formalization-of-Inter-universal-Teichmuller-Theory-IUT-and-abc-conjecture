import tmp.sheaf.xif.paper.S348OrbifoldMu2lInterfaceActual
/-! # S370: conditional theta-section log-volume interface on S346/S348
Only an interface/Prop is constructed: a set-level log-volume function on the
abstract O^tri carrier, with actuality/compatibility flags kept as Prop fields.
No measure and no numerical log-volume is faked.  The exact missing interface is
recorded as Nonempty. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
namespace LeanFormal.IUT.XiFPaper.S370ThetaSectionLogVolumeInterfaceActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S346OrbifoldStructuralSheafActual
open LeanFormal.IUT.XiFPaper.S348OrbifoldMu2lInterfaceActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable (C : OrbifoldStructuralSheafCarrierSpec T b)
variable (I : OrbifoldMu2lInterface T b C)
/-- Conditional set-level log-volume interface.  The numeric function is
interface data; actuality and compatibility are Props, not asserted. -/
structure ThetaSectionLogVolumeInterface
    (C : OrbifoldStructuralSheafCarrierSpec T b)
    (I : OrbifoldMu2lInterface T b C) where
  logVolume : Set C.carrier → Real
  actualLogVolume : Prop
  orbitCompatibility : Prop
/-- Set-level placeholder: evaluate the interface function on the theta union. -/
noncomputable def thetaSectionLogVolumePlaceholder
    (L : ThetaSectionLogVolumeInterface T b C I) : Real :=
  L.logVolume (thetaOrbitUnion T b I)
/-- The placeholder is definitionally the interface function at the union. -/
theorem thetaSectionLogVolumePlaceholder_eq
    (L : ThetaSectionLogVolumeInterface T b C I) :
    thetaSectionLogVolumePlaceholder T b C I L =
      L.logVolume (thetaOrbitUnion T b I) := rfl
/-- Exact missing log-volume interface: no inhabitant is asserted. -/
def ThetaSectionLogVolumeInterfaceRequired : Prop :=
  Nonempty (ThetaSectionLogVolumeInterface T b C I)
/-- Exact missing actual-log-volume condition: the interface flags an actual
log-volume only if its own Prop field is inhabited; this is not claimed. -/
def ThetaSectionLogVolumeActual : Prop :=
  ∃ L : ThetaSectionLogVolumeInterface T b C I, L.actualLogVolume
end LeanFormal.IUT.XiFPaper.S370ThetaSectionLogVolumeInterfaceActual
