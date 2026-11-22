import tmp.sheaf.n8.closure.EtaSignedCriterionDisproof
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIndexResidueFormula

/-!
# Eta volume-index formula attempt

Production gives the log-shell integer index only conditionally on the
q/e/f residue-cardinality hypothesis:

  logShellIntegerIndex =
    residueCard ^ (e * s - 1) * (residueCard - 1) / #torsion.

At the native F-place this gives an exact formula for fPlaceVolumeIndex.  The
signed criterion therefore reduces to

  residueCard ^ (e*s-1) * (residueCard - 1) / #torsion
    = residueNormBase ^ order.

The current native data does not supply the q/e/f hypothesis at the
F-place, nor a relation between the q order and e/f.  We record the conditional
actual formula and the exact remaining arithmetic gap; no normalization is
arbitrary and no equality is assumed.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaVolumeIndexFormulaAttempt

open scoped Padic

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open LeanFormal.IUT.N8Closure.EtaFPlaceSignedComparison
open LeanFormal.IUT.N8Closure.EtaSignedCriterionDisproof
open LeanFormal.IUT.Foundations.LocalFields.LogShellVolume
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open ABCBridge.N8.C3TensorTargetCorrection
open LeanFormal.IUT.ArithmeticQPilotBaseChange

variable {l : PrimeGeFive}
variable {X : N8NativeInput l}

/-- Conditional q/e/f hypothesis at the actual F-place. -/
abbrev FPlaceQFE (X : N8NativeInput l) (e f : Nat) : Prop :=
  LogShellQFECardinalityHypothesis (K := FPlaceCompletion X)
    (p := nativePrime X) e f

/-- Conditional production formula for the F-place volume index. -/
theorem fPlaceVolumeIndex_eq_qfeFormula {e f : Nat}
    (X : N8NativeInput l) (h : FPlaceQFE X e f) :
    fPlaceVolumeIndex X =
      logShellResidueCard (K := FPlaceCompletion X) ^
          (e * logShellScaleExponentFactor (p := nativePrime X) - 1) *
        (logShellResidueCard (K := FPlaceCompletion X) - 1) /
          Nat.card (CommGroup.torsion
            (Integers (FPlaceCompletion X))ˣ) := by
  unfold fPlaceVolumeIndex fPlaceVolumeConsumer
  exact logShellIntegerIndex_eq_residueCard_pow_mul_sub_one_div_torsion_of_qfe
    (K := FPlaceCompletion X) (p := nativePrime X) h

/-- Exact q/e/f arithmetic gap for the signed criterion. -/
def EtaVolumeIndexQFEFormulaGap (X : N8NativeInput l) (e f : Nat) : Prop :=
  ((logShellResidueCard (K := FPlaceCompletion X) ^
        (e * logShellScaleExponentFactor (p := nativePrime X) - 1) *
      (logShellResidueCard (K := FPlaceCompletion X) - 1) /
        Nat.card (CommGroup.torsion
          (Integers (FPlaceCompletion X))ˣ) : Nat) : Real) =
    ArithmeticQPilotBaseChange.residueNormBase (nativeFPlaceOverBad X) ^
      (C9QPilotRegion.nativeQ X).order

/-- Under the production q/e/f formula, the signed criterion is exactly the
above integer arithmetic equation. -/
theorem signedCriterion_iff_qfeFormulaGap {e f : Nat}
    (X : N8NativeInput l) (h : FPlaceQFE X e f) :
    EtaFPlaceSignedComparisonTarget X ↔
      EtaVolumeIndexQFEFormulaGap X e f := by
  rw [signedCriterion_iff_index_eq_residueNormBase_pow]
  rw [fPlaceVolumeIndex_eq_qfeFormula X h]
  rw [EtaVolumeIndexQFEFormulaGap]

/-- Exact missing production data: the q/e/f hypothesis at the F-place and the
relation between q order and e/f are not supplied; only the conditional formula
above is available. -/
def EtaVolumeIndexFormulaMissingData (X : N8NativeInput l) : Prop :=
  ∀ e f : Nat, FPlaceQFE X e f →
    EtaVolumeIndexQFEFormulaGap X e f

end LeanFormal.IUT.N8Closure.EtaVolumeIndexFormulaAttempt
