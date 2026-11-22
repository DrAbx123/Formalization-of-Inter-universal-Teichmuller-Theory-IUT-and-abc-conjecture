/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HaarStrictRPActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import Mathlib.Tactic

/-!
# Mzk1HaarStrictRPInstanceActual — the genuine `R/p` radius instance (A558)

Instantiation of the general strictly-smaller-radius theorem with
`r b = R_b / p_b`, `p_b = qVFamTensorP T b` (the residue characteristic at `b`).
This is the genuine nonarchimedean strictly smaller ball: `R/p < R` since
`p_b > 1`, whereas `R/2` can be the same valuation class for odd `p_b`.

Proved here: positivity/strictness of the radius, the region's containment in
the hull, its positive finite product measure, and the positive cylinder disjoint
from the region.  (The final strict Haar inequality is the additivity step.) -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HaarStrictRPInstanceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictRPActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The `R/p` radius at a bad place. -/
noncomputable def rP (b : Bad (nativePlaceSelection T)) : Real :=
  (rootImageRadius T b : Real) / (qVFamTensorP T b : Real)

theorem rP_pos (b : Bad (nativePlaceSelection T)) : 0 < rP T b := by
  unfold rP
  have hR : (0 : Real) < (rootImageRadius T b : Real) :=
    NNReal.coe_pos.mpr (rootImageRadius_pos (T := T) (b := b))
  have hp : (1 : Real) < (qVFamTensorP T b : Real) := by
    have hprime : Nat.Prime (qVFamTensorP T b) := Fact.out
    exact_mod_cast hprime.one_lt
  exact div_pos hR (by linarith)

theorem rP_lt (b : Bad (nativePlaceSelection T)) :
    rP T b < (rootImageRadius T b : Real) := by
  unfold rP
  have hR : (0 : Real) < (rootImageRadius T b : Real) :=
    NNReal.coe_pos.mpr (rootImageRadius_pos (T := T) (b := b))
  have hp : (1 : Real) < (qVFamTensorP T b : Real) := by
    have hprime : Nat.Prime (qVFamTensorP T b) := Fact.out
    exact_mod_cast hprime.one_lt
  have hden : (0 : Real) < (qVFamTensorP T b : Real) := by linarith
  rw [div_lt_iff₀ hden]
  nlinarith

/-- The genuine `R/p` q-region. -/
noncomputable def qRegionRP : Set (S1902Carrier T) :=
  qRegionR T (rP T)

theorem qRegionRP_subset_hull : qRegionRP T ⊆ s1902Hull T :=
  qRegionR_subset_hull T (rP T) (rP_pos T) (rP_lt T)

theorem qRegionRP_measure_pos : 0 < rootExtensionProductHaar T (qRegionRP T) :=
  qRegionR_measure_pos T (rP T) (rP_pos T)

theorem qRegionRP_measure_lt_top : rootExtensionProductHaar T (qRegionRP T) < ⊤ :=
  qRegionR_measure_lt_top T (rP T)

/-- The `R/p` cylinder at an attaining place. -/
noncomputable def annulusCylinderRP (b0 : Bad (nativePlaceSelection T))
    (y : rootNormedExtension T b0) : Set (S1902Carrier T) :=
  annulusCylinderR T (rP T) b0 y

theorem annulusCylinderRP_subset_hull (b0 : Bad (nativePlaceSelection T))
    (y : rootNormedExtension T b0)
    (hy : ‖y‖ = (rootImageRadius T b0 : Real)) :
    annulusCylinderRP T b0 y ⊆ s1902Hull T :=
  annulusCylinderR_subset_hull T (rP T) (rP_pos T) (rP_lt T) b0 y hy

theorem annulusCylinderRP_disjoint (b0 : Bad (nativePlaceSelection T))
    (y : rootNormedExtension T b0)
    (hy : ‖y‖ = (rootImageRadius T b0 : Real)) :
    Disjoint (annulusCylinderRP T b0 y) (qRegionRP T) :=
  annulusCylinderR_disjoint_qRegionR T (rP T) (rP_pos T) (rP_lt T) b0 y hy

#check qRegionRP_subset_hull
#check qRegionRP_measure_pos
#check annulusCylinderRP_disjoint

end LeanFormal.IUT.XiFPaper.Mzk1HaarStrictRPInstanceActual
end
