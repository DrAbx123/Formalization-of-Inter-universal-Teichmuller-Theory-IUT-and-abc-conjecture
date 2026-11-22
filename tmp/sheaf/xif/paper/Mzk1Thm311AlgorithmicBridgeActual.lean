import tmp.sheaf.gogopex.Iut.Foundations.AlgorithmicBridge

/-! Mainline (A517-3): the algorithmic-output bridge used for the 3.11 => 3.11.5 step
(Gogopex `AlgorithmicBridge`), referenced as a real object: a certified algorithmic output
plus a source-specific `CommonTargetBoundBridge` yields measured common-target bounds and
preserves the IPL/SHE/APT properties.  All theorems below are the Gogopex real declarations,
re-exported under our namespace. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Thm311AlgorithmicBridgeActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open Iut RealLineCopy

universe u

section Bridge

variable {source target : Copy} {index : Type u}
variable (output : AlgorithmicOutput source target index)
variable (measure : RegionMeasure target) (bound : ℝ)

/-- **O2 object**: the common-target-bound bridge of the algorithmic output (the abstract
  place where the 3.11 => 3.11.5 step lives). -/
structure Thm311CommonTargetBoundBridge where
  /-- The Gogopex bridge structure. -/
  bridge : AlgorithmicOutput.CommonTargetBoundBridge output measure bound

/-- Apply the bridge to a certified output, producing the certified common-target bound. -/
def Thm311CommonTargetBoundBridge.apply
    (B : Thm311CommonTargetBoundBridge output measure bound)
    (certified : output.Certified) :
    output.CertifiedCommonTargetBound measure bound :=
  B.bridge.apply certified

/-- **Measured common-target bound** at any choice (Gogopex real theorem). -/
theorem thm311_choice_targetVolume_le
    (B : Thm311CommonTargetBoundBridge output measure bound)
    (certified : output.Certified) (choice : index) :
    RegionMeasure.targetVolume measure (output.comparison choice) ≤ bound :=
  AlgorithmicOutput.CommonTargetBoundBridge.choice_targetVolume_le B.bridge certified choice

/-- **All targets are bounded** (Gogopex real theorem). -/
theorem thm311_allTargetsAtMost
    (B : Thm311CommonTargetBoundBridge output measure bound)
    (certified : output.Certified) :
    RegionComparisonFamily.AllTargetsAtMost measure output.comparisons bound :=
  AlgorithmicOutput.CommonTargetBoundBridge.allTargetsAtMost B.bridge certified

/-- **IPL is preserved by the bridge** (Gogopex real theorem). -/
theorem thm311_preserves_hasIPL
    (B : Thm311CommonTargetBoundBridge output measure bound)
    (certified : output.Certified) : output.HasIPL :=
  AlgorithmicOutput.CommonTargetBoundBridge.preserves_hasIPL B.bridge certified

/-- **SHE is preserved by the bridge** (Gogopex real theorem). -/
theorem thm311_preserves_hasSHE
    (B : Thm311CommonTargetBoundBridge output measure bound)
    (certified : output.Certified) : output.HasSHE :=
  AlgorithmicOutput.CommonTargetBoundBridge.preserves_hasSHE B.bridge certified

/-- **APT is preserved by the bridge** (Gogopex real theorem). -/
theorem thm311_preserves_hasAPT
    (B : Thm311CommonTargetBoundBridge output measure bound)
    (certified : output.Certified) : output.HasAPT :=
  AlgorithmicOutput.CommonTargetBoundBridge.preserves_hasAPT B.bridge certified

end Bridge

end

end LeanFormal.IUT.XiFPaper.Mzk1Thm311AlgorithmicBridgeActual