/-
INVALID AS PAPER OBJECT (completion 2l-th root audit).

This file depends on a completion 2l-th root q_v^(1/2l) of the qVFamily q
(PaperQRootCard / NatRootSystem (qVUnit ...) / HalfRootInCompletion).
S342QVFamilyRootImpossibleActual proves that this is impossible: the order is
coprime to l while a 2l-th root forces 2l | order.  The conditional records
and consequences below are retained only as invalidated history; they must not
be used as paper objects or as inputs to further constructions.
-/
import tmp.sheaf.xif.paper.BadPlaceRootHullScalingFormulaActual
import tmp.sheaf.xif.paper.PaperC3ThetaRootActual

/-! # Half-root generator supply at c_norm/(2l)

The completion has no general 2l-th root of the qVFamily normalized generator.
The actual 2l-root lives in the algebraic closure (twoLthRootAt), not in the
normalized completion.  This file packages the minimal actual half-root datum
in the completion: a unit whose 2l-th power is the normalized generator and
whose norm is p^{-(c_norm/(2l))}.  From such a datum the S122 half scaling data
and scaling formula follow.  No root is fabricated.

No sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.BadPlaceHalfRootSupplyActual

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
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
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

/-- The actual normalized generator place as a CommonPrimeCompletion. -/
abbrev halfRootPlace : FinitePlaceAtPrime T.arithmetic.F (qVFamTensorP T b) :=
  (qVFamTensorPlaces T b) () ()

/-- Minimal actual half-root datum in the completion. -/
structure HalfRootInCompletion where
  root : (CommonPrimeCompletion (halfRootPlace T b))ˣ
  pow_twoL : root ^ (2 * l.value) = qVFamNormalizedGenerator T b
  norm_eq : ‖(root : CommonPrimeCompletion (halfRootPlace T b))‖ =
    (qVFamTensorP T b : Real) ^
      (-(QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b /
        (2 * l.value : Real)))

/-- The half-generator supply obtained from an actual half-root datum. -/
noncomputable def halfGeneratorSupplyOfRoot
    (R : HalfRootInCompletion T b) :
    RootHullHalfGeneratorSupply T b where
  generator := R.root
  generator_norm := R.norm_eq

/-- Half scaling data from an actual half-root datum. -/
noncomputable def halfScalingDataOfRoot
    (R : HalfRootInCompletion T b) :
    ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (halfCoefficientFamily T b) :=
  rootHullHalfScalingData T b (halfGeneratorSupplyOfRoot T b R)

/-- Exact hull equality plus half-root datum gives the S122 gap. -/
noncomputable def halfScalingDataGapOfRoot
    (R : HalfRootInCompletion T b)
    (hull_eq : actualLocalHullRegion (l := l) T b =
      ((arithmeticTupleFractionalLattice
          (qVFamTensorPlaces T b) qVFamTensorTuple (halfCoefficientFamily T b) *
        arithmeticTupleHolomorphicLattice
          (qVFamTensorPlaces T b) qVFamTensorTuple :
          Submodule ℤ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)) :
        Set (qVFamTensorBlock T b))) :
    RootHullHalfScalingDataGap T b where
  supply := halfGeneratorSupplyOfRoot T b R
  hull_eq := hull_eq

/-- Conditional root-hull scaling formula from a half-root datum. -/
theorem rootHullScalingFormulaAt_of_halfRoot
    (R : HalfRootInCompletion T b)
    (hull_eq : actualLocalHullRegion (l := l) T b =
      ((arithmeticTupleFractionalLattice
          (qVFamTensorPlaces T b) qVFamTensorTuple (halfCoefficientFamily T b) *
        arithmeticTupleHolomorphicLattice
          (qVFamTensorPlaces T b) qVFamTensorTuple :
          Submodule ℤ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)) :
        Set (qVFamTensorBlock T b))) :
    RootHullScalingFormulaAt T b :=
  rootHullScalingFormulaAt_of_halfScalingData T b
    (halfScalingDataGapOfRoot T b R hull_eq)

/-- Exact missing half-root source condition. -/
def HalfRootCompletionGap : Prop :=
  Nonempty (HalfRootInCompletion T b)

end LeanFormal.IUT.XiFPaper.BadPlaceHalfRootSupplyActual
