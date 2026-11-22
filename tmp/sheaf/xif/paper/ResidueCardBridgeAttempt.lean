import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIndexResidueFormula
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalInputs
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.ArithmeticQPilotBaseChange

namespace LeanFormal.IUT.XiFPaper.ResidueCardBridgeAttempt

variable {K : Type*} [Field K] [NumberField K]

/-- The log-shell residue cardinality is the arithmetic ideal absolute norm. -/
theorem logShellResidueCard_eq_absNorm
    (place : NumberField.FinitePlace K) :
    logShellResidueCard (K := NormalizedCompletion place) =
      Ideal.absNorm place.maximalIdeal.asIdeal := by
  unfold logShellResidueCard logShellResidueField
  rw [show Nat.card (IsLocalRing.ResidueField
        (Integers (NormalizedCompletion place))) =
      Nat.card (IsLocalRing.ResidueField (CompletionIntegers place)) from
    Nat.card_congr
      (IsLocalRing.ResidueField.mapEquiv
        (normalizedCompletionIntegersEquiv place)).toEquiv]
  rw [show Nat.card (IsLocalRing.ResidueField (CompletionIntegers place)) =
      Nat.card (NumberField.RingOfIntegers K ⧸ place.maximalIdeal.asIdeal) from
    Nat.card_congr
      (NumberFieldFinitePlace.residueEquivAdicCompletionIntegers
        (K := K) place).toEquiv.symm]
  rw [Ideal.absNorm_apply]
  exact (Submodule.cardQuot_apply _).symm

/-- The log-shell residue cardinal is the base residue norm. -/
theorem logShellResidueCard_eq_residueNormBase
    (place : NumberField.FinitePlace K) :
    (logShellResidueCard (K := NormalizedCompletion place) : ℝ) = residueNormBase place := by
  unfold residueNormBase
  rw [logShellResidueCard_eq_absNorm place]

end LeanFormal.IUT.XiFPaper.ResidueCardBridgeAttempt
