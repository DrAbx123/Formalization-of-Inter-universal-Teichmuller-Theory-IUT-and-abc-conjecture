import tmp.sheaf.xif.paper.BadPlaceRootHullScalingFormulaActual
import tmp.sheaf.xif.paper.Mzk1Stage4ScalingDirectionStudyActual

/-! # Mzk1Stage4HullScalingFormulaConsumerActual (stage4 lane; hull scaling consumer)

A655 module: stage4 consumer of the EXACT hull scaling formula (other-lane source
`BadPlaceRootHullScalingFormulaActual`, READ only): the formula holds conditionally on
the minimal half-scaling data, and the S117 correction vanishes.  Together with the
scaling-direction study this is the DECISION POINT evidence for the forward direction.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4HullScalingFormulaConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.BadPlaceRootHullScalingFormulaActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4ScalingDirectionStudyActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Stage4 consumer: the exact root-hull scaling formula from the minimal half-scaling
data. -/
theorem stage4_hull_scaling_formula {b : Bad (nativePlaceSelection T)}
    (G : RootHullHalfScalingDataGap (l := l) T b) :
    RootHullScalingFormulaAt (l := l) T b :=
  rootHullScalingFormulaAt_of_halfScalingData (l := l) T b G

/-- Stage4 consumer: the S117 coefficient correction vanishes from actual half-scaling
data. -/
theorem stage4_correction_eq_zero
    (G : ∀ b : Bad (nativePlaceSelection T), RootHullHalfScalingDataGap (l := l) T b) :
    thetaHullCoefficientCorrection (l := l) T = 0 :=
  thetaHullCoefficientCorrection_eq_zero_of_halfScalingData (l := l) T G

/-- The decision-point record: exact hull formula + scaling-direction evidence. -/
def decisionPointRows : List (String × String) :=
  [ ("exact hull scaling formula", "conditional on RootHullHalfScalingDataGap (rootHullScalingFormulaAt_of_halfScalingData)")
  , ("S117 correction", "vanishes from actual half-scaling data")
  , ("scaling direction", "FORWARD (growing) model holds Gap 1; INVERSE fails (counterexample ε=1, triple (2,0,0))")
  , ("conclusion", "forward triple-dependent scaling is the correction candidate; paper conclusion unchanged")
  ]

/-- The decision-point record has four rows. -/
theorem decisionPointRows_length : decisionPointRows.length = 4 := rfl

#check stage4_hull_scaling_formula
#check stage4_correction_eq_zero
#check decisionPointRows
#check decisionPointRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Stage4HullScalingFormulaConsumerActual
end
