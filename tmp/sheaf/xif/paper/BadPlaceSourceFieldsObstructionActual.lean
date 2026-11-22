import tmp.sheaf.xif.paper.BadPlacePaperTargetStrictActual
/-! # Exact obstruction to PaperSourceCorrectionFreeFields

PaperSourceCorrectionFreeFields requires the pointwise norm-ratio equality
qVFamNormRatio_b = 1 and the pointwise root-hull scaling formula.  The actual
definitions give qVFamNormRatio = normalized spectral norm / default valuation
norm, two different norm instances on the same completion; the ratio is one
exactly when those norms agree.  This file records that exact obstruction and
the root-hull scaling obstruction.  No correction=0 is faked.

No sorry/axiom/True/PUnit. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.BadPlaceSourceFieldsObstructionActual
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
open LeanFormal.IUT.XiFPaper.BadPlaceRootHullScalingFormulaActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperTargetStrictActual
open LeanFormal.IUT.XiFPaper.PaperBadPlaceTensorGeometryActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open MeasureTheory
open LeanFormal.IUT.ArithmeticQPilotBaseChange
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
/-- The norm-ratio obstruction at b. -/
def NormRatioObstructionAt : Prop := qVFamNormRatio T b ≠ 1
/-- The root-hull scaling obstruction at b. -/
def RootHullScalingObstructionAt : Prop := ¬ RootHullScalingFormulaAt T b
/-- Global norm-ratio obstruction. -/
def NormRatioObstruction : Prop :=
  ∃ b : Bad (nativePlaceSelection T), NormRatioObstructionAt T b
/-- Global root-hull scaling obstruction. -/
def RootHullScalingObstruction : Prop :=
  ∃ b : Bad (nativePlaceSelection T), RootHullScalingObstructionAt T b
/-- Norm ratio one is exactly equality of the two actual norm instances. -/
theorem qVFamNormRatio_eq_one_iff_norm_eq :
    qVFamNormRatio T b = 1 ↔ qVFamNormalizedNorm T b = qVFamDefaultNorm T b := by
  unfold qVFamNormRatio
  have hdef : qVFamDefaultNorm T b ≠ 0 := by
    unfold qVFamDefaultNorm
    exact norm_ne_zero_iff.mpr (qVFamily T b).q_ne_zero
  constructor
  · intro h
    exact (div_eq_one_iff_eq hdef).mp h
  · intro h
    rw [h, div_self hdef]
/-- Exact nonvanishing obstruction in terms of the norm-instance gap. -/
theorem normRatioObstructionAt_iff_norm_ne :
    NormRatioObstructionAt T b ↔ qVFamNormalizedNorm T b ≠ qVFamDefaultNorm T b := by
  unfold NormRatioObstructionAt
  exact not_congr (qVFamNormRatio_eq_one_iff_norm_eq T b)
/-- Exact obstruction to PaperSourceCorrectionFreeFields. -/
theorem papersourceFields_iff_no_obstruction :
    Nonempty (PaperSourceCorrectionFreeFields T) ↔
      ¬ NormRatioObstruction T ∧ ¬ RootHullScalingObstruction T := by
  constructor
  · rintro ⟨S⟩
    constructor
    · rintro ⟨b, hb⟩
      exact hb (S.normRatio_one b)
    · rintro ⟨b, hb⟩
      exact hb (S.rootHull_scaling b)
  · rintro ⟨hN, hS⟩
    refine ⟨⟨?_, ?_⟩⟩
    · intro b
      by_contra hb
      exact hN ⟨b, hb⟩
    · intro b
      by_contra hb
      exact hS ⟨b, hb⟩
/-- Construct the fields from the two exact pointwise inputs. -/
noncomputable def paperSourceCorrectionFreeFieldsOf
    (hN : NormRatioObstruction T → False)
    (hS : RootHullScalingObstruction T → False) :
    PaperSourceCorrectionFreeFields T where
  normRatio_one b := by
    by_contra hb
    exact hN ⟨b, hb⟩
  rootHull_scaling b := by
    by_contra hb
    exact hS ⟨b, hb⟩
/-- Constructive fields from the direct pointwise equalities. -/
noncomputable def paperSourceCorrectionFreeFieldsOfPointwise
    (hN : ∀ b : Bad (nativePlaceSelection T), qVFamNormRatio T b = 1)
    (hS : ∀ b : Bad (nativePlaceSelection T), RootHullScalingFormulaAt T b) :
    PaperSourceCorrectionFreeFields T where
  normRatio_one := hN
  rootHull_scaling := hS
end LeanFormal.IUT.XiFPaper.BadPlaceSourceFieldsObstructionActual
