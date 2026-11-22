/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1AnnulusMeasurePositiveActual
import Mathlib.Tactic

/-!
# Mzk1AnnulusStrictConsumerActual — strict Haar increase discharged (A557)

Consumes the cylinder geometry (`Mzk1HaarAnnulusCylinderActual`), the conditional
strict theorem (`Mzk1HaarStrictProofActual`) and the cylinder measure positivity
(`Mzk1AnnulusMeasurePositiveActual`) to prove, unconditionally:

  `(μ qRegionHalf).toReal < (μ hull).toReal`  and the resolved
  `PositiveQRegionHaarStrict T`.

No `sorry`, no axiom; the half-ball `qRegionHalf` is the honest positive-measure
log-shell region (singletons are Haar-null). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1AnnulusStrictConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarAnnulusCylinderActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictProofActual
open LeanFormal.IUT.XiFPaper.Mzk1AnnulusMeasurePositiveActual
open LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureQRegionProofActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Measurability of the explicit cylinder product set. -/
theorem cylinderProduct_measurable (b0 : Bad (nativePlaceSelection T))
    (y : rootNormedExtension T b0) :
    MeasurableSet (cylinderProduct T b0 y) := by
  unfold cylinderProduct
  apply MeasurableSet.pi Set.countable_univ
  intro b
  by_cases hb : b = b0
  · subst hb
    simpa using measurableSet_closedBall
  · simp only [dif_neg hb]
    exact measurableSet_closedBall

/-- **Unconditional strict Haar increase**: the hull has strictly larger product
Haar measure than the positive-measure half-ball q-region. -/
theorem haarStrict (b0 : Bad (nativePlaceSelection T)) :
    (rootExtensionProductHaar T (qRegionHalf T)).toReal <
      (rootExtensionProductHaar T (s1902Hull T)).toReal := by
  apply haarStrict_of_cylinder_measure T b0
  · rw [annulusCylinder_eq_cylinderProduct]
    exact cylinderProduct_measurable T b0 (attainingValue T b0)
  · rw [annulusCylinder_eq_cylinderProduct]
    exact cylinderProduct_measure_pos T b0 (attainingValue T b0)

/-- The resolved `PositiveQRegionHaarStrict`: q_pos and strict_measure are now
THEOREMS from Haar data. -/
theorem positiveQRegionHaarStrict (b0 : Bad (nativePlaceSelection T)) :
    PositiveQRegionHaarStrict T :=
  positiveQRegionHaarStrict_of_cylinder T b0
    (cylinderProduct_measurable T b0 (attainingValue T b0))
    (by
      rw [annulusCylinder_eq_cylinderProduct]
      exact cylinderProduct_measure_pos T b0 (attainingValue T b0))

#check haarStrict
#check positiveQRegionHaarStrict

end LeanFormal.IUT.XiFPaper.Mzk1AnnulusStrictConsumerActual
end
