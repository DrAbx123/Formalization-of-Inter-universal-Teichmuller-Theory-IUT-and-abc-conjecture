import tmp.sheaf.n8.closure.EtaSelectedPlaceReadout
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Eta q versus volume-index comparison

The selected readout is

  etaSelectedLogVolume X = Real.log (volumeIndex X),
  etaPilotQ X            = nativeQParameter X (badNativeBadPlace X).

The native qParameter is exp(-exponent) with exponent a positive integer, hence
0 < etaPilotQ X < log 2.  The volume index is a positive natural number.
If the gap EtaSelectedPlaceQPilotGap X held, then

  volumeIndex X = Real.exp (etaPilotQ X) < 2,

so volumeIndex = 1 and etaSelectedLogVolume = 0.  But etaPilotQ > 0, a
contradiction.  Therefore the equality is false for every native X.

This is a decisive no-go for the raw equality; it does not assert a replacement
equality.  No arbitrary equality or common Real carrier is used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaQVolumeIndexComparison

open scoped Padic

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeQParameterActual
open LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt
open LeanFormal.IUT.N8Closure.NativePartitionInputsActual
open LeanFormal.IUT.N8Closure.NativeBadFintypeSourceAttempt
open LeanFormal.IUT.N8Closure.NativeBadFiniteTargetCorrection
open LeanFormal.IUT.N8Closure.NativeReductionRestActual
open LeanFormal.IUT.N8Closure.EtaIntegralStructureAtSelectedPlaceRoute
open LeanFormal.IUT.N8Closure.EtaIntegralStructureSourceBridgeRoute
open LeanFormal.IUT.N8Closure.EtaSelectedPlaceReadoutRoute
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.Foundations.LocalFields.LogShellVolume
open LeanFormal.IUT.ConcreteFiniteTheorem311

variable {l : PrimeGeFive}
variable {X : N8NativeInput l}

/-- Unfolding of the selected log-volume readout. -/
theorem etaSelectedLogVolume_eq_log_index (X : N8NativeInput l) :
    etaSelectedLogVolume X =
      Real.log (((etaIntegralStructureAtSelectedPlace X).volume.index : Nat) : Real) :=
  rfl

/-- Unfolding of the etaPilot q readout. -/
theorem etaPilotQ_eq_nativeQParameter (X : N8NativeInput l) :
    etaPilotQ X = nativeQParameter X (badNativeBadPlace X) :=
  rfl

theorem etaPilotQ_pos (X : N8NativeInput l) : 0 < etaPilotQ X := by
  rw [etaPilotQ_eq_nativeQParameter]
  exact Real.exp_pos _

/-- The native qParameter is below log 2, because its exponent is a positive
integer and exp(-1) < log 2. -/
theorem etaPilotQ_lt_log_two (X : N8NativeInput l) :
    etaPilotQ X < Real.log 2 := by
  rw [etaPilotQ_eq_nativeQParameter]
  change Real.exp (-((nativeQExponent X (badNativeBadPlace X) : Int) : Real)) <
    Real.log 2
  have hpos : 0 < nativeQExponent X (badNativeBadPlace X) :=
    nativeQExponent_pos X (badNativeBadPlace X)
  have hge : (1 : Real) ≤ ((nativeQExponent X (badNativeBadPlace X) : Int) : Real) := by
    exact_mod_cast hpos
  have harg : -((nativeQExponent X (badNativeBadPlace X) : Int) : Real) ≤ -1 := by
    linarith
  have hqle : Real.exp (-((nativeQExponent X (badNativeBadPlace X) : Int) : Real)) ≤
      Real.exp (-1) :=
    Real.exp_le_exp.mpr harg
  have hhalf : Real.exp (-1) < (1 / 2 : Real) := Real.exp_neg_one_lt_half
  have hlog : (1 / 2 : Real) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  exact lt_of_le_of_lt hqle (lt_trans hhalf hlog)

/-- Decisive no-go: the raw selected-logVolume = etaPilot equality is false. -/
theorem etaSelectedPlaceQPilotGap_false (X : N8NativeInput l) :
    ¬ EtaSelectedPlaceQPilotGap X := by
  intro h
  have hlog : Real.log
      (((etaIntegralStructureAtSelectedPlace X).volume.index : Nat) : Real) =
      etaPilotQ X := by
    change etaSelectedLogVolume X = etaPilotQ X at h
    simpa [etaSelectedLogVolume_eq_log_index] using h
  have hidxpos_nat : 0 < (etaIntegralStructureAtSelectedPlace X).volume.index :=
    (etaIntegralStructureAtSelectedPlace X).volume.index_pos
  have hidxpos : (0 : Real) <
      (((etaIntegralStructureAtSelectedPlace X).volume.index : Nat) : Real) := by
    exact_mod_cast hidxpos_nat
  have hexp : Real.exp (etaPilotQ X) =
      (((etaIntegralStructureAtSelectedPlace X).volume.index : Nat) : Real) := by
    rw [← hlog, Real.exp_log hidxpos]
  have hlt2 : (((etaIntegralStructureAtSelectedPlace X).volume.index : Nat) : Real) < 2 := by
    rw [← hexp]
    have h := Real.exp_lt_exp.mpr (etaPilotQ_lt_log_two X)
    rwa [Real.exp_log (by norm_num : (0 : Real) < 2)] at h
  have hidxlt2 : (etaIntegralStructureAtSelectedPlace X).volume.index < 2 := by
    exact_mod_cast hlt2
  have hidx_one : (etaIntegralStructureAtSelectedPlace X).volume.index = 1 := by
    omega
  have hlogzero : Real.log
      (((etaIntegralStructureAtSelectedPlace X).volume.index : Nat) : Real) = 0 := by
    rw [hidx_one]
    norm_num
  have hqpos : 0 < etaPilotQ X := etaPilotQ_pos X
  rw [hlogzero] at hlog
  linarith

/-- Exact source condition that would be required for the raw gap; it is false
by the theorem above. -/
def EtaQVolumeIndexSourceCondition (X : N8NativeInput l) : Prop :=
  EtaSelectedPlaceQPilotGap X

theorem etaQVolumeIndexSourceCondition_false (X : N8NativeInput l) :
    ¬ EtaQVolumeIndexSourceCondition X :=
  etaSelectedPlaceQPilotGap_false X

end LeanFormal.IUT.N8Closure.EtaQVolumeIndexComparison
