/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HaarAnnulusCylinderActual
import tmp.sheaf.xif.paper.Mzk1HaarStrictActual
import tmp.sheaf.xif.paper.Mzk1PositiveMeasureQRegionProofActual
import Mathlib.Tactic

/-!
# Mzk1HaarStrictProofActual — attaining label, cylinder geometry, conditional strict Haar

A553: the annulus argument completed up to the single Haar fact
`0 < μ(annulusCylinder)` (product of positive closed-ball factors; translation
invariance already available).  Proved here:
* `exists_attaining_label`: at each bad place a theta label attains the hull radius
  (`Finset.exists_mem_eq_sup`);
* `attainingValue_norm`: the attaining value has norm exactly `R_b0`;
* `annulusCylinder_attaining_subset_hull` / `..._disjoint`: the cylinder is inside
  the hull and disjoint from the half-ball q-region;
* `haarStrict_of_cylinder_measure`: **conditional strict Haar theorem** from
  measurability + positive cylinder measure (the last named Haar fact). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HaarStrictProofActual

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
open LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureQRegionProofActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- At every bad place some theta label attains the hull radius. -/
theorem exists_attaining_label (b0 : Bad (nativePlaceSelection T)) :
    ∃ j : ThetaLabel (l := l),
      (⟨‖(rootNormedThetaValueInL T b0 (thetaLabelToSigned (l := l) j) :
          rootNormedExtension T b0)‖, norm_nonneg _⟩ : NNReal) =
        rootImageRadius T b0 := by
  classical
  haveI : Nonempty (ThetaLabel (l := l)) := ⟨oneThetaLabel l⟩
  unfold rootImageRadius
  exact Finset.exists_mem_eq_sup Finset.univ (Finset.univ_nonempty)
    (fun j : ThetaLabel (l := l) =>
      (⟨‖(rootNormedThetaValueInL T b0 (thetaLabelToSigned (l := l) j) :
          rootNormedExtension T b0)‖, norm_nonneg _⟩ : NNReal))

/-- The chosen attaining label at `b0`. -/
noncomputable def attainingLabel (b0 : Bad (nativePlaceSelection T)) :
    ThetaLabel (l := l) :=
  Classical.choose (exists_attaining_label T b0)

/-- The theta value `y` attaining the hull radius at `b0`. -/
noncomputable def attainingValue (b0 : Bad (nativePlaceSelection T)) :
    rootNormedExtension T b0 :=
  rootNormedThetaValueInL T b0 (thetaLabelToSigned (l := l) (attainingLabel T b0))

/-- The attaining value has norm equal to the hull radius. -/
theorem attainingValue_norm (b0 : Bad (nativePlaceSelection T)) :
    ‖attainingValue T b0‖ = (rootImageRadius T b0 : Real) := by
  have h := Classical.choose_spec (exists_attaining_label T b0)
  have h' : (⟨‖attainingValue T b0‖, norm_nonneg _⟩ : NNReal) = rootImageRadius T b0 := by
    simpa [attainingValue, attainingLabel] using h
  exact_mod_cast congrArg NNReal.toReal h'

/-- The cylinder is contained in the hull. -/
theorem annulusCylinder_attaining_subset_hull (b0 : Bad (nativePlaceSelection T)) :
    annulusCylinder T b0 (attainingValue T b0) ⊆ s1902Hull T :=
  annulusCylinder_subset_hull T b0 (attainingValue T b0)
    (attainingValue_norm T b0)
    (by exact_mod_cast rootImageRadius_pos (T := T) (b := b0))

/-- The cylinder is disjoint from the half-ball qRegion. -/
theorem annulusCylinder_attaining_disjoint (b0 : Bad (nativePlaceSelection T)) :
    Disjoint (annulusCylinder T b0 (attainingValue T b0)) (qRegionHalf T) :=
  annulusCylinder_disjoint_qRegionHalf T b0 (attainingValue T b0)
    (attainingValue_norm T b0)
    (by exact_mod_cast rootImageRadius_pos (T := T) (b := b0))

/-- **Conditional strict Haar increase**: measurability and positive measure of the
cylinder give `(μ qRegionHalf).toReal < (μ hull).toReal`. -/
theorem haarStrict_of_cylinder_measure (b0 : Bad (nativePlaceSelection T))
    (hmeas : MeasurableSet (annulusCylinder T b0 (attainingValue T b0)))
    (hpos : 0 < rootExtensionProductHaar T
      (annulusCylinder T b0 (attainingValue T b0))) :
    (rootExtensionProductHaar T (qRegionHalf T)).toReal <
      (rootExtensionProductHaar T (s1902Hull T)).toReal :=
  haarStrict_of_positive_annulus T (annulusCylinder T b0 (attainingValue T b0))
    hmeas (annulusCylinder_attaining_subset_hull T b0)
    (annulusCylinder_attaining_disjoint T b0) hpos

/-- The resolved `PositiveQRegionHaarStrict` from the conditional strict theorem. -/
theorem positiveQRegionHaarStrict_of_cylinder (b0 : Bad (nativePlaceSelection T))
    (hmeas : MeasurableSet (annulusCylinder T b0 (attainingValue T b0)))
    (hpos : 0 < rootExtensionProductHaar T
      (annulusCylinder T b0 (attainingValue T b0))) :
    PositiveQRegionHaarStrict T :=
  positiveQRegionHaarStrict_of_strict T
    (ENNReal.toReal_pos (ne_of_gt (qRegionHalf_measure_pos T))
      (ne_of_lt (qRegionHalf_measure_lt_top T)))
    (haarStrict_of_cylinder_measure T b0 hmeas hpos)

#check exists_attaining_label
#check haarStrict_of_cylinder_measure

end LeanFormal.IUT.XiFPaper.Mzk1HaarStrictProofActual
end
