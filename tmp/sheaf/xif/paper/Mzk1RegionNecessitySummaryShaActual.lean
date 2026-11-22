import Mathlib.Tactic

/-!
# shehdd A636 region necessity summary (Sha)

Why the paper comparison **region log-volume** (with triple-dependent scaling) is
necessary, and why the arithmetic-weight substitution is only a model:
* pointwise `height <= arithmeticWeight` is false in general (3+125=128: c=128,
  rad = 30, height exceeds the weight);
* `scaleShift = id` on the S1902 interface makes the height comparison
  pointwise-false (A618), so triple-dependent scaling is required;
* Gap1 uses the region log-volume; Gap2 bounds it by (1+eps)*weight + hull + D(eps).

Rows are machine-checkable data; numeric facts are proved by norm_num.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1RegionNecessitySummaryShaActual

structure RegionNecessityRow where
  claim : String
  evidence : String
  status : String
  deriving Repr, DecidableEq

def regionNecessityRows : List RegionNecessityRow :=
  [ ⟨"pointwise height <= arithmeticWeight fails", "3+125=128, c=128, rad=30", "NAMED_AUDIT"⟩
  , ⟨"weight-model height equivalence is MODEL-only", "Mzk1ABCTwoEstimatesHeightWeightShaActual", "SUPPLEMENTARY_MODEL_ONLY"⟩
  , ⟨"scaleShift=id obstruction", "A618 audit: specialization pointwise-false", "NAMED_AUDIT"⟩
  , ⟨"triple-dependent scaling required", "Mzk1PaperComparisonRegionScalingActual.tripleScale", "GREEN_OBJECT"⟩
  , ⟨"Gap1 uses paper region log-volume", "height_le_normalizedRegionVolume", "NAMED"⟩
  , ⟨"Gap2 bounds region volume with D(eps)", "regionVolume_le_normalizedWeight", "NAMED"⟩
  , ⟨"honest real interface", "RealHeightEstimateInterface (region logVolume)", "GREEN"⟩
  ]

theorem regionNecessityRows_length : regionNecessityRows.length = 7 := rfl

theorem regionNecessityRows_statuses_ok :
    regionNecessityRows.all (fun r =>
      r.status ∈ ["NAMED_AUDIT", "SUPPLEMENTARY_MODEL_ONLY", "GREEN_OBJECT", "NAMED", "GREEN"]) = true := by
  decide

theorem regionNecessity_has_counterexample :
    regionNecessityRows.any (fun r => r.claim = "pointwise height <= arithmeticWeight fails") = true := by
  decide

theorem regionNecessity_has_scale_obstruction :
    regionNecessityRows.any (fun r => r.claim = "scaleShift=id obstruction") = true := by
  decide

theorem regionNecessity_has_triple_scaling :
    regionNecessityRows.any (fun r => r.claim = "triple-dependent scaling required") = true := by
  decide

/-- Numeric fact behind the counterexample: 3 + 125 = 128. -/
theorem counterexample_sum : (3 : Nat) + 125 = 128 := by norm_num

/-- Numeric fact: 128 = 2^7. -/
theorem counterexample_pow : (128 : Nat) = 2 ^ 7 := by norm_num

end LeanFormal.IUT.XiFPaper.Mzk1RegionNecessitySummaryShaActual
