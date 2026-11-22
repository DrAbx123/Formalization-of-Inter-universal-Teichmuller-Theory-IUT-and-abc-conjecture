import tmp.sheaf.xif.paper.Mzk1CorrectedRegionLogLawBlockersActual

/-! # Mzk1Stage4CorrectedRegionLogLawB3Actual (stage4 lane; B3 log arithmetic)

A666 module: the B3 blocker of the corrected-region log law — the LOG ARITHMETIC
`log (∏_b (ofReal primeFactor_b ^ e_b)⁻¹).toReal = -Σ_b e_b log (ofReal primeFactor_b).toReal`,
proved in abstract finite-product form.  B1 (null singletons) and B2 (normalization split)
remain hull/mainline items.  Mainline blockers file READ only; no object changed.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4CorrectedRegionLogLawB3Actual

open scoped ENNReal BigOperators

/-- B3 (single factor): `log ((a^n)⁻¹).toReal = -n log a.toReal` for finite nonzero `a`. -/
theorem log_toReal_inv_pow {a : ENNReal} (ha0 : a ≠ 0) (haT : a ≠ ⊤) (n : Nat) :
    Real.log (((a ^ n)⁻¹).toReal) = -(n : Real) * Real.log a.toReal := by
  have hane : a.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨ha0, haT⟩
  rw [ENNReal.toReal_inv, ENNReal.toReal_pow]
  rw [Real.log_inv, Real.log_pow]
  ring

/-- B3 (finite product): the log of the inverse prime-power product is minus the
weighted sum of the factor logarithms. -/
theorem log_toReal_prod_inv_pow {ι : Type*} (s : Finset ι) (f : ι → ENNReal)
    (e : ι → Nat) (h0 : ∀ i ∈ s, f i ≠ 0) (hT : ∀ i ∈ s, f i ≠ ⊤) :
    Real.log ((∏ i ∈ s, ((f i) ^ (e i))⁻¹).toReal) =
      -∑ i ∈ s, (e i : Real) * Real.log (f i).toReal := by
  rw [ENNReal.toReal_prod]
  have hterm : ∀ i ∈ s, (((f i) ^ (e i))⁻¹).toReal = ((f i).toReal ^ (e i))⁻¹ := by
    intro i hi
    rw [ENNReal.toReal_inv, ENNReal.toReal_pow]
  -- rewrite each factor
  have hcongr : (∏ i ∈ s, (((f i) ^ (e i))⁻¹).toReal) =
      ∏ i ∈ s, (((f i).toReal ^ (e i))⁻¹) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact hterm i hi
  rw [hcongr]
  have hprodlog : Real.log (∏ i ∈ s, ((f i).toReal ^ (e i))) =
      ∑ i ∈ s, (e i : Real) * Real.log (f i).toReal := by
    rw [Real.log_prod]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [Real.log_pow]
    · intro i hi
      have hane : (f i).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨h0 i hi, hT i hi⟩
      exact pow_ne_zero _ hane
  rw [Finset.prod_inv_distrib, Real.log_inv, hprodlog]

/- B3 status: the log arithmetic is proved above; B1/B2 belong to hull/mainline. -/

#check log_toReal_inv_pow
#check log_toReal_prod_inv_pow

end LeanFormal.IUT.XiFPaper.Mzk1Stage4CorrectedRegionLogLawB3Actual
end
