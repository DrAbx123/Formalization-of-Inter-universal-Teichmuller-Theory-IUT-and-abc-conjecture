/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HaarStrictProofActual
import tmp.sheaf.xif.paper.Mzk1PositiveMeasureQRegionProofActual
import Mathlib.Tactic

/-!
# Mzk1AnnulusMeasurePositiveActual — cylinder product measure positivity (A557)

The last Haar fact: the annulus cylinder is a finite product set, hence its
product Haar measure is the product of positive closed-ball factor measures
(`Measure.pi_pi` + `Metric.addHaar_closedBall_center` + local closed-ball
positivity), giving `0 < μ cylinder`.  Combined with the cylinder geometry this
discharges `haarStrict_of_cylinder_measure`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1AnnulusMeasurePositiveActual

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
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b0 : Bad (nativePlaceSelection T))
variable (y : rootNormedExtension T b0)

/-- The cylinder as an explicit finite product set. -/
def cylinderProduct : Set (S1902Carrier T) :=
  Set.pi Set.univ (fun b =>
    if h : b = b0 then
      Metric.closedBall (h.symm ▸ y) ((rootImageRadius T b0 : Real) / 4)
    else
      Metric.closedBall (0 : rootNormedExtension T b)
        (rootImageRadius T b : Real))

/-- The cylinder equals its product form. -/
theorem annulusCylinder_eq_cylinderProduct :
    annulusCylinder T b0 y = cylinderProduct T b0 y := by
  ext x
  simp only [annulusCylinder, cylinderProduct, Set.mem_setOf_eq, Set.mem_pi,
    Set.mem_univ, forall_true_left, Metric.mem_closedBall, dist_eq_norm]
  constructor
  · rintro ⟨h1, h2⟩ b
    by_cases hb : b = b0
    · subst hb
      simpa using h1
    · simp [hb, h2 b hb]
  · intro hx
    constructor
    · have := hx b0
      simpa using this
    · intro b hb
      have := hx b
      simpa [hb] using this

/-- The product-measure formula for the cylinder. -/
theorem cylinderProduct_measure :
    rootExtensionProductHaar T (cylinderProduct T b0 y) =
      ∏ b : Bad (nativePlaceSelection T),
        (if h : b = b0 then
          rootExtensionHaar T b (Metric.closedBall (h.symm ▸ y)
            ((rootImageRadius T b0 : Real) / 4))
        else
          rootExtensionHaar T b (Metric.closedBall
            (0 : rootNormedExtension T b) (rootImageRadius T b : Real))) := by
  unfold rootExtensionProductHaar cylinderProduct
  rw [Measure.pi_pi]

theorem rootImageRadius_coe_pos (b : Bad (nativePlaceSelection T)) :
    (0 : Real) < (rootImageRadius T b : Real) :=
  NNReal.coe_pos.mpr (rootImageRadius_pos (T := T) (b := b))

/-- The cylinder has positive product Haar measure. -/
theorem cylinderProduct_measure_pos :
    0 < rootExtensionProductHaar T (cylinderProduct T b0 y) := by
  rw [cylinderProduct_measure]
  apply Finset.prod_pos
  intro b _
  by_cases hb : b = b0
  · subst hb
    simp only [dif_pos rfl]
    rw [Metric.addHaar_closedBall_center]
    apply rootExtensionClosedBall_measure_pos
    have hR := rootImageRadius_coe_pos T b
    linarith
  · simp only [dif_neg hb]
    apply rootExtensionClosedBall_measure_pos
    exact rootImageRadius_coe_pos T b

/-- The annulus cylinder has positive product Haar measure. -/
theorem annulusCylinder_measure_pos :
    0 < rootExtensionProductHaar T (annulusCylinder T b0 y) := by
  rw [annulusCylinder_eq_cylinderProduct]
  exact cylinderProduct_measure_pos T b0 y

end LeanFormal.IUT.XiFPaper.Mzk1AnnulusMeasurePositiveActual
end
