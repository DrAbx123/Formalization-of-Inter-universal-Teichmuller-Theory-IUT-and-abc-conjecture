import Mathlib.Tactic

/-!
# shehdd A641 A618 machine-proof audit rows (Sha)

Diagnostic audit of the mainline-owned `Mzk1A618MachineProofActual` (read-only):
* the needed lemma `comparisonRegion_eq_hull` does NOT exist in
  `Mzk1S1902ComparisonRegionActual`; the actual proved lemmas are
  `comparisonRegion_eq_unscaled` and `comparisonRegion_eq_unitRegion_of_mem`;
* `comparisonRegion` is `unitRegion ∪ {point}`, so applying the finite-hull
  obstruction `no_constantRegion_heightComparison` with the full hull requires an
  inclusion/equality that is not available; the green obstruction
  `identity_scaleShift_obstruction` (A618ScalingObstructionActual) proves the
  unit-region form directly;
* the Fintype synth failures come from the `nativePlaceSelection` ambiguity
  (root vs `N8Closure` namespaces);
* conclusion: the machine-proof file needs redesign, not a local fix.  This audit
  file is evidence only; no mainline file is changed.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1A618MachineProofAuditShaActual

structure MachineProofAuditRow where
  issue : String
  evidence : String
  suggestedAction : String
  status : String
  deriving Repr, DecidableEq

def machineProofAuditRows : List MachineProofAuditRow :=
  [ ⟨"missing lemma comparisonRegion_eq_hull", "not in Mzk1S1902ComparisonRegionActual (actual: comparisonRegion_eq_unscaled, comparisonRegion_eq_unitRegion_of_mem)", "use comparisonRegion_eq_unscaled or drop the hull-region step", "RED"⟩
  , ⟨"region shape", "comparisonRegion = s1902UnitRegion T union {point}", "apply no_constantRegion_heightComparison to unitRegion, not hull", "RED"⟩
  , ⟨"Fintype Bad nativePlaceSelection", "ambiguous term (root vs N8Closure)", "open LeanFormal.IUT.N8Closure and use bare nativePlaceSelection, or fully qualify", "RED"⟩
  , ⟨"green replacement", "Mzk1A618ScalingObstructionActual.identity_scaleShift_obstruction (gate trio)", "reuse instead of new machine proof", "GREEN_SOURCE"⟩
  , ⟨"conclusion", "machine-proof file needs redesign", "mainline owner action; evidence only here", "AUDIT"⟩
  ]

theorem machineProofAuditRows_length : machineProofAuditRows.length = 5 := rfl

theorem machineProofAuditRows_statuses_ok :
    machineProofAuditRows.all (fun r =>
      r.status ∈ ["RED", "GREEN_SOURCE", "AUDIT"]) = true := by
  decide

theorem machineProofAudit_has_missing_lemma :
    machineProofAuditRows.any (fun r => r.issue = "missing lemma comparisonRegion_eq_hull") = true := by
  decide

theorem machineProofAudit_has_green_replacement :
    machineProofAuditRows.any (fun r => r.status = "GREEN_SOURCE") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1A618MachineProofAuditShaActual
