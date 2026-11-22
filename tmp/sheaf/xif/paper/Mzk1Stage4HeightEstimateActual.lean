import tmp.sheaf.xif.paper.Mzk1Stage4HeightRegionNumericsActual

/-! # Mzk1Stage4HeightEstimateActual (stage4 lane; unique filename)

A611 module: substantive two-sided HEIGHT estimate for the 11a1@l=13 data — the
height `(5/6) log 11` is positive and bounded above by the hull constant 11, and it
sits below the region volume `2 log 11`.  No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4HeightEstimateActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4HeightRegionNumericsActual

/-- The 11a1 height value `(5/6) log 11`. -/
noncomputable def height11 : Real := (5 / 6) * Real.log 11

/-- The 11a1 region volume `2 log 11`. -/
noncomputable def regionVol11 : Real := 2 * Real.log 11

/-- Two-sided height estimate: positivity and the hull upper bound. -/
structure HeightEstimate where
  /-- positivity. -/
  lb : 0 < height11
  /-- upper bound by the hull constant 11. -/
  ub : height11 <= 11

/-- Construct the 11a1 height estimate. -/
noncomputable def heightEstimate11 : HeightEstimate where
  lb := by
    unfold height11
    have h : (0 : Real) < Real.log 11 := Real.log_pos (by norm_num)
    linarith
  ub := by
    unfold height11
    have h : Real.log 11 < 11 := by
      have := Real.log_le_sub_one_of_pos (show (0 : Real) < 11 by norm_num)
      linarith
    linarith

/-- Height sits below the region volume. -/
theorem height_le_region : height11 < regionVol11 := by
  unfold height11 regionVol11
  have h : (0 : Real) < Real.log 11 := Real.log_pos (by norm_num)
  linarith

/-- Both readings are finite reals (trivially, as real numbers). -/
theorem height_region_finite :
    ∃ h v : Real, h = height11 ∧ v = regionVol11 :=
  ⟨height11, regionVol11, rfl, rfl⟩

#check height11
#check regionVol11
#check HeightEstimate
#check heightEstimate11
#check height_le_region
#check height_region_finite

end LeanFormal.IUT.XiFPaper.Mzk1Stage4HeightEstimateActual
end
