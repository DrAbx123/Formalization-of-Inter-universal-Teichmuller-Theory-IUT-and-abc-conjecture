import tmp.sheaf.n8.closure.EtaPartialShellLogAction
import tmp.sheaf.n8.closure.EtaShellActionReadoutActual
import LeanFormal.IUT.IUTII.Kummer.VerticalLogKummerOrderedLayer

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaShellDepthScalingActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaLogLinkCommonClosure
open LeanFormal.IUT.N8Closure.EtaAdditiveLogTransportActual
open LeanFormal.IUT.N8Closure.EtaPartialShellLogAction
open LeanFormal.IUT.N8Closure.EtaShellActionReadoutActual
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open ABCBridge.N8.C3TensorTargetCorrection
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

/-- Corrected real additive readout: the production unit-shell depth of the
embedded F-shell unit.  It is a real log-depth, not a multiplicative norm-log. -/
noncomputable def shellDepth (u : (fPlaceShell X).Units) : ℝ :=
  unitShellDepth (nativePrime X) (fShellUnitToAlgClUnit X u)

/-! ## Corrected scaling law -/

/-- Actual scaling: the production root-system iterate scales the real
unit-shell depth by `1/(m+1)`.  This is the correct additive/division
scaling, not the false norm-log multiplicative division. -/
theorem shellDepth_scaling (m : Nat) (_hm : m ≠ 0)
    (u : (fPlaceShell X).Units) (h : u ∈ goodShellUnit X m 1) :
    shellDepth X (partialShellAction X m 1 u h) =
      shellDepth X u / ((m + 1 : Nat) : ℝ) := by
  have hv := partialShellAction_spec X m 1 u h
  have hroot : fShellUnitToAlgClUnit X (partialShellAction X m 1 u h) =
      rootSystemPowRoot (nativePrime X) (m + 1) (fShellUnitToAlgClUnit X u) := by
    rw [hv, layerUnitAction_one]
  rw [shellDepth, hroot, unitShellDepth_rootSystemPowRoot (p := nativePrime X) (hN := Nat.succ_ne_zero m)]
  rfl

/-! ## qPilot/qO agreement target -/

/-- Exact agreement target: the corrected depth readout agrees with the
actual qO region log-volume.  The production qO volume identity is
`qORegionLogVolume = qPilotSignedLog`; the missing item is the norm/log
normalization between depth and the qO real volume. -/
def EtaShellDepthQPilotAgreement : Prop :=
  ∀ u : (fPlaceShell X).Units, shellDepth X u = qORegionLogVolume X

def EtaShellDepthQPilotAgreementGap : Prop :=
  ¬ EtaShellDepthQPilotAgreement X

/-! ## Exact gap -/

/- The scaling law is actual.  The remaining exact gap is the agreement of
the depth readout with `qORegionLogVolume` (equivalently qPilot).  No
arbitrary readout or normalization is introduced. -/
end LeanFormal.IUT.N8Closure.EtaShellDepthScalingActual
