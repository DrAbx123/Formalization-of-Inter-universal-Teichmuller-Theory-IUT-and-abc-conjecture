# O6 / M2 pin donors (sophie adapter handoff, 2026-11-17 13:26)

Part 1 adapter: `Mzk1GChoiceToM2Actual` DONE 13:11:42 (exact-name re-exports only):
- `gChoice_criticalValues_rat_adapter` = `Mzk1GChoiceUnramifiedCanonicalActual.canonicalBelyi_criticalValues_row`
- `gChoice_unramified_infty_adapter` = `...gPoly_unramified_infty`
- `gChoice_avoids_adapter` = `Mzk1GChoiceAvoidCanonicalActual.gChoice_avoids`
- `gChoice_card_lt_adapter` = `...gChoice_card_lt`
- `gChoice_unramified_of_criticalInTarget_adapter` = `Mzk1GChoiceUnramifiedCanonicalActual.gChoice_unramified_of_criticalInTarget`
- `gChoiceData_of_avoids_adapter` = `Mzk1GChoiceAvoidCanonicalActual.gChoiceData_of_avoids`
- `polyEvalP1_specialSet_iff_adapter` = `Mzk1G1PsiM2AnalyticActual.polyEvalP1_ofFinite_mem_specialSet_iff`

Part 2 (`Mzk1GChoiceToM2BridgedActual`, in progress): for henry's `M2BranchPinObligation`
1. `gPoly_natDegree_pos_adapter (D) : 0 < (gPoly D).natDegree`
2. `gPoly_derivative_ne_zero_adapter (D) : derivative (gPoly D) ≠ 0`
3. `gPoly_criticalValues_subset_adapter (D) : {v | exists z, aeval z (derivative (gPoly D)) = 0
   and aeval z (gPoly D) = v} ⊆ {0, (critFrac D : C)}`  (the CLOSEST TRUE raw form: raw
   gPoly critical values are {0, critFrac D}, NOT {0,1})
4. `gPolyNorm (D) := C (critFrac D)^{-1} * gPoly D` and
   `gPolyNorm_criticalValues_subset (D) : ... ⊆ {0,1}`  (normalized form; this is the pin input)
5. `gPoly_beta_avoiding_p1 (D) (H) : AvoidsPoint (polyMorphism (gPoly D) ...) D.beta ...`
   `gPoly_beta_not_mem_image (D) (H) : D.beta ∉ ↑(D.S.image (polyMapPoints (gPoly D)))`
6. `gPoly_value_mem_rat (D) {z} (h : aeval z (gPoly D) = 0) : ∃ c : ℚ, aeval z (gPoly D) = algebraMap ℚ ℂ c`

Call shape for the pin (3 lines):
```lean
-- pin critical values to {0,1}:
have hpin := gPolyNorm_criticalValues_subset D
-- beta avoidance (0 is not a branch value):
have hbeta := gPoly_beta_not_mem_image D H
-- rational value transfer for a zero branch:
obtain ⟨c, hc⟩ := gPoly_value_mem_rat D hz
```

NOTE: the raw `gPoly` does NOT have critical values in {0,1} (they are {0, critFrac D});
the pin must go through the normalized `gPolyNorm` (scale by critFrac^{-1}).  This is a
found real distinction, not a missing lemma.
