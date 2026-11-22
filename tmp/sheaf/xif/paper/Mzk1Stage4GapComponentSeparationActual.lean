import tmp.sheaf.xif.paper.Mzk1Stage4ABCGapEstimatesActual

/-! # Mzk1Stage4GapComponentSeparationActual (stage4 lane; gap components)

A641 module (Gap1/Gap2 progress): structural component separation for the two gaps —
each gap structure is exactly its bound, and the two components can be transported
independently.  No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4GapComponentSeparationActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual

/-- Gap 1 component: the structure is equivalent to its bound. -/
theorem gap1_iff (height regionVol : Real) :
    Gap1 height regionVol ↔ height ≤ regionVol :=
  ⟨fun h => h.bound, fun h => ⟨h⟩⟩

/-- Gap 2 component: the structure is equivalent to its bound. -/
theorem gap2_iff (regionVol weight hull D eps : Real) :
    Gap2 regionVol weight hull D eps ↔
      regionVol ≤ (1 + eps) * weight + hull + D :=
  ⟨fun h => h.bound, fun h => ⟨h⟩⟩

/-- Gap 1 transport: monotonicity of the left slot. -/
theorem gap1_mono_left {height height' regionVol : Real}
    (h : Gap1 height regionVol) (hle : height' ≤ height) :
    Gap1 height' regionVol :=
  ⟨le_trans hle h.bound⟩

/-- Gap 2 transport: enlarging the right-hand constant preserves the bound. -/
theorem gap2_mono_D {regionVol weight hull D D' eps : Real}
    (h : Gap2 regionVol weight hull D eps) (hDD : D ≤ D') :
    Gap2 regionVol weight hull D' eps :=
  ⟨by linarith [h.bound]⟩

#check gap1_iff
#check gap2_iff
#check gap1_mono_left
#check gap2_mono_D

end LeanFormal.IUT.XiFPaper.Mzk1Stage4GapComponentSeparationActual
end
