import tmp.sheaf.xif.paper.BadPlaceThetaHullCorrectionFormulaActual

/-! # Root-hull scaling formula: conditional actual data and exact gap

RootHullScalingFormulaAt states

  actualLocalHullLog_b = - (c_norm_b/(2l)) * log p_b.

The available actual scaling data is at c_norm, not at c_norm/(2l); the
2l-root generator is missing.  This file constructs the minimal actual supply
at c_norm/(2l), derives the actual fractional-lattice scaling data from it, and
proves the scaling formula under the exact missing hull-equality datum.  Without
that datum the formula remains an exact gap.

No fake formula. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.BadPlaceRootHullScalingFormulaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperConstantsActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormalizationSourceActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootComparisonActual
open LeanFormal.IUT.XiFPaper.BadPlaceCorrectionControlActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormRatioCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormRatioSourceActual
open LeanFormal.IUT.XiFPaper.BadPlaceCorrectionSignActual
open LeanFormal.IUT.XiFPaper.BadPlaceCorrectionSignAttackActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedTargetBridgeActual
open LeanFormal.IUT.XiFPaper.BadPlaceThetaHullScalarBridgeActual
open LeanFormal.IUT.XiFPaper.BadPlaceThetaHullCorrectionFormulaActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.PaperBadPlaceTensorGeometryActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The half coefficient c_norm/(2l) as a tensor coefficient family. -/
noncomputable def halfCoefficientFamily : qVFamTensorV → Real :=
  fun _ => QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b /
    (2 * l.value : Real)

/-- Minimal actual generator supply at the half coefficient. -/
abbrev RootHullHalfGeneratorSupply : Type :=
  NormalizedGeneratorSupplyAt T b
    (QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b /
      (2 * l.value : Real))

/-- Actual fractional-lattice scaling data at c_norm/(2l), from a half-generator
supply. -/
noncomputable def rootHullHalfScalingData
    (S : RootHullHalfGeneratorSupply T b) :
    ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (halfCoefficientFamily T b) :=
  arithmeticTuplePureFractionalScalingData_ofGenerator
    (qVFamTensorPlaces T b) qVFamTensorTuple
    (halfCoefficientFamily T b)
    (fun _ => S.generator) (fun _ => S.generator_norm)

/-- Exact minimal hull/scaling data required for the formula. -/
structure RootHullHalfScalingDataGap where
  supply : RootHullHalfGeneratorSupply T b
  hull_eq : actualLocalHullRegion (l := l) T b =
    ((arithmeticTupleFractionalLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple (halfCoefficientFamily T b) *
      arithmeticTupleHolomorphicLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple :
        Submodule ℤ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)) :
      Set (qVFamTensorBlock T b))

/-- The exact root-hull scaling formula follows from the minimal hull/scaling
actual data. -/
theorem rootHullScalingFormulaAt_of_halfScalingData
    (G : RootHullHalfScalingDataGap T b) :
    RootHullScalingFormulaAt T b := by
  unfold RootHullScalingFormulaAt thetaCoefficientContribution
  unfold actualLocalHullLog
  rw [G.hull_eq]
  rw [arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    (qVFamTensorPlaces T b) qVFamTensorTuple Measure.addHaar
    (c := halfCoefficientFamily T b) (rootHullHalfScalingData T b G.supply)]
  unfold halfCoefficientFamily
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_eq_one_iff.mpr ⟨(), by intro x; cases x; rfl⟩]
  simp

/-- Conditional vanishing of the S117 correction from actual half-scaling data. -/
theorem thetaHullCoefficientCorrection_eq_zero_of_halfScalingData
    (G : ∀ b : Bad (nativePlaceSelection T), RootHullHalfScalingDataGap T b) :
    thetaHullCoefficientCorrection (l := l) T = 0 :=
  thetaHullCoefficientCorrection_eq_zero_of_scaling_formula T
    (fun b => rootHullScalingFormulaAt_of_halfScalingData T b (G b))

end LeanFormal.IUT.XiFPaper.BadPlaceRootHullScalingFormulaActual
