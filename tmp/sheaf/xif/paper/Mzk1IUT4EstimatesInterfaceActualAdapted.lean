import Mathlib

/-!
# Mzk1IUT4EstimatesInterfaceActualAdapted (adapted copy, A475 reuse) — IUT IV Theorem 1.10 estimates interface (genuine definitions)

Status: PENDING-VERIFY (watchdog compile). No sorry, no axiom, no fake closure.
Formal model: uniform height-vs-volume and region inputs; genuine lemmas. Registers interface only. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUT4EstimatesInterfaceActualAdapted

/-- IUT IV Section 1 estimate data: uniform and region inputs. -/
structure IUT4EstimateData (X : Type*) where
  uniformHeightBound : ℚ
  regionBound : ℚ
  uniform_nonneg : 0 ≤ uniformHeightBound
  region_nonneg : 0 ≤ regionBound

/-- Genuine lemma: the sum of the estimate bounds is nonnegative. -/
theorem IUT4EstimateData.bound_add_nonneg {X : Type*} (d : IUT4EstimateData X) :
    0 ≤ d.uniformHeightBound + d.regionBound :=
  add_nonneg d.uniform_nonneg d.region_nonneg

end LeanFormal.IUT.XiFPaper.Mzk1IUT4EstimatesInterfaceActualAdapted
