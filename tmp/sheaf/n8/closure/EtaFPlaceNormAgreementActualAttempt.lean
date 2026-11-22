import tmp.sheaf.n8.closure.EtaFPlaceLogNormAgreementActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport

/-!
# Eta F-place norm agreement attempt / decisive no-go

Production normative facts:
- normalizedCompletion_norm_le_one_iff compares unit balls only;
- completionMap norm transport gives native norm = (base norm)^(relativeCompletionDegree)
  on base completion images.

At the native F-place the normalized F-completion norm and the native
completion norm carry different Qp normalizations.  The decisive relation is

  native norm = normalized norm ^ relativeCompletionDegree.

If that power relation holds for the native q unit, then

  FPlaceNormAgreement  <->  relativeCompletionDegree = 1.

For a nontrivial extension (degree > 1) the exact norm agreement is false in
general; the unit-ball comparison is insufficient.  This file proves the
conditional equivalence and records the exact power-relation dependency.  No
arbitrary normalization is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaFPlaceNormAgreementActualAttempt

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaFPlaceLogNormAgreementActual
open LeanFormal.IUT.N8Closure.EtaQOClassReadoutNormalizedActual
open LeanFormal.IUT.N8Closure.EtaQORegionMassNormFromScaling
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open ABCBridge.N8.C3TensorTargetCorrection

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Relative completion degree of the native F-place over the base Fmod place. -/
noncomputable abbrev relDegree : ℕ :=
  relativeCompletionDegree (k := X.S.arithmetic.Fmod) (nativeFPlaceAtPrime X).val

/-- Native completion value of the q unit. -/
def nativeQVal : Completion (nativeFPlaceOverBad X) :=
  (C9QPilotRegion.nativeQ X).q

/-- Normalized F-completion value of the transported q unit. -/
def normalizedQVal : KfX X :=
  ((nativeQUnitKf X) : KfX X)

/-- Exact power relation between native and normalized norms. -/
def NativeNormPowerRelation : Prop :=
  ‖nativeQVal X‖ = ‖normalizedQVal X‖ ^ relDegree X

/-- Conditional decisive no-go: power relation + non-unit norm forces degree one. -/
theorem fPlaceNormAgreement_iff_degree_one_of_power
    (hpow : NativeNormPowerRelation X)
    (hne0 : ‖normalizedQVal X‖ ≠ 0)
    (hne1 : ‖normalizedQVal X‖ ≠ 1) :
    FPlaceNormAgreement X ↔ relDegree X = 1 := by
  have hpos : 0 < ‖normalizedQVal X‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne0)
  constructor
  · intro hagree
    have hagree1 : ‖normalizedQVal X‖ = ‖nativeQVal X‖ := by
      simpa [FPlaceNormAgreement, nativeQVal, normalizedQVal] using hagree
    have hlog : Real.log (‖normalizedQVal X‖ ^ relDegree X) =
        Real.log ‖normalizedQVal X‖ := by
      rw [← hpow]
      exact congrArg Real.log hagree1.symm
    rw [Real.log_pow] at hlog
    have hlog_ne : Real.log ‖normalizedQVal X‖ ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one hpos hne1
    have hcast : ((relDegree X : ℝ) - 1) * Real.log ‖normalizedQVal X‖ = 0 := by
      calc
        ((relDegree X : ℝ) - 1) * Real.log ‖normalizedQVal X‖ =
            (relDegree X : ℝ) * Real.log ‖normalizedQVal X‖ -
              Real.log ‖normalizedQVal X‖ := by ring
        _ = Real.log ‖normalizedQVal X‖ - Real.log ‖normalizedQVal X‖ := by rw [hlog]
        _ = 0 := sub_self _
    have hsub : (relDegree X : ℝ) - 1 = 0 := by
      rcases mul_eq_zero.mp hcast with h | h
      · exact h
      · exact absurd h hlog_ne
    have hdeg : (relDegree X : ℝ) = 1 := by linarith
    exact_mod_cast hdeg
  · intro hdeg
    have hnat : ‖nativeQVal X‖ = ‖normalizedQVal X‖ := by
      rw [NativeNormPowerRelation] at hpow
      rw [hdeg, pow_one] at hpow
      exact hpow
    simpa [FPlaceNormAgreement, nativeQVal, normalizedQVal] using hnat.symm

/-- Exact norm-agreement dependency: the native/normalized power relation. -/
theorem fPlaceNormAgreement_requires_power_relation :
    NativeNormPowerRelation X ↔
      ‖nativeQVal X‖ = ‖normalizedQVal X‖ ^ relDegree X :=
  Iff.rfl

/-- The unit-ball comparison alone gives no exact norm equality: it is only an
inequality on both unit balls.  This is recorded as the decisive no-go
dependency; the power relation and its degree-one condition are the exact
missing ingredients. -/
def FPlaceNormUnitBallOnlyNoGo : Prop :=
  FPlaceNormAgreement X → NativeNormPowerRelation X

end LeanFormal.IUT.N8Closure.EtaFPlaceNormAgreementActualAttempt
