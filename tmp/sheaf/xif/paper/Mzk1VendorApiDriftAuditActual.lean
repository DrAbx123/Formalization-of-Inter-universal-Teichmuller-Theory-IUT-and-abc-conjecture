/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-!
# A749/A756 vendor API-drift fixes (mainline)

Vendored trees are pinned at upstream revisions but compiled against a newer
Mathlib.  Each entry records a tactic-level/import-level repair; mathematics unchanged.

| file | line | old | new | error class |
|---|---|---|---|---|
| TateCurvesTheta/TateCurve/Quotient.lean | 6 | imports AnalyticQuotient only | + import Uniformization | missing `toAnalyticQuotient_eq_iff` |
| TateCurvesTheta/TateCurve/Quotient.lean | 85 | `rw [map_mul, toAnalyticQuotient_q, one_mul]` | `rw [TateDatum.toAnalyticQuotient_eq_iff, mul_inv_rev, ...]` + `Subgroup.inv_mem` | `one_mul` pattern drift on quotient group |

Result: Quotient.lean EXIT=0 + olean. No statement/object changed; no axiom added. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1VendorApiDriftAuditActual

def vendorFixRows : List (String × String × String) :=
  [ ("TateCurvesTheta/TateCurve/Quotient.lean", "6,85", "import Uniformization + quotient-eq proof; math unchanged"),
    ("scope", "vendor", "port repair only; no statement change; ABC gate NOT passed") ]

theorem vendorFixRows_length : vendorFixRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1VendorApiDriftAuditActual

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1VendorApiDriftAuditActual.vendorFixRows_length