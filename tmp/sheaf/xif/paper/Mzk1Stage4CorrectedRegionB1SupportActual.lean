import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-! # Mzk1Stage4CorrectedRegionB1SupportActual (stage4 lane; B1 abstract reduction)

A667 module: the B1 blocker of the corrected-region log law, reduced to its abstract
form — a PRODUCT measure of a singleton is zero when every coordinate measure of the
coordinate singleton is zero (Mathlib `Measure.pi_singleton`).  The per-coordinate
nullity for `rootExtensionHaar` remains a hull-lane fact (B1 concrete); B2
(normalization split) remains mainline.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4CorrectedRegionB1SupportActual

open MeasureTheory
open scoped ENNReal BigOperators

universe u v

/-- B1 abstract: the product measure of a singleton is zero when every coordinate
singleton is null. -/
theorem pi_singleton_null {ι : Type u} [Fintype ι] [Nonempty ι]
    {α : ι → Type v} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (f : ∀ i, α i)
    (h : ∀ i, μ i {f i} = 0) : Measure.pi μ {f} = 0 := by
  rw [Measure.pi_singleton]
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact Finset.prod_eq_zero (Finset.mem_univ i) (h i)

/-- B1 concrete-form statement (reduction): if the coordinate Haar measures of
singletons vanish, then the product Haar of the product singleton vanishes. -/
theorem pi_singleton_null_pointwise {ι : Type u} [Fintype ι] [Nonempty ι]
    {α : ι → Type v} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, α i)
    (h : ∀ i, μ i {f i} = 0) : Measure.pi μ {f} = 0 :=
  pi_singleton_null μ f h

/-- B1 status rows. -/
def b1Rows : List (String × String) :=
  [ ("B1 abstract", "pi_singleton_null: product singleton null from coordinate nullity")
  , ("B1 concrete", "coordinate rootExtensionHaar {x} = 0 (hull lane)")
  , ("B2 normalization", "s1902NormalizedHaar/s1902LogVolume smul unwrap (mainline)")
  , ("B3 log arithmetic", "stage4 CorrectedRegionLogLawB3Actual (PROVED here)")
  ]

/-- The B1 record has four rows. -/
theorem b1Rows_length : b1Rows.length = 4 := rfl

#check pi_singleton_null
#check pi_singleton_null_pointwise
#check b1Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1Stage4CorrectedRegionB1SupportActual
end
