import tmp.sheaf.xif.paper.Mzk1Cor312BoundsActual
import tmp.sheaf.xif.paper.Mzk1TargetABCInterfaceActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1ABCTargetBoundsBundleActualAdapted (adapted copy, A475 reuse) — Cor312 bounds + ABC target-data bundle

Reuses EXIT0 Cor312 bound bookkeeping and the ABC target-data interface to expose
the combined bound/slack inequality and the pointwise height<=weight+bound law.
No paper bound is proved; no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTargetBoundsBundleActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1Cor312BoundsActual
open LeanFormal.IUT.XiFPaper.Mzk1TargetABCInterfaceActual

structure ABCTargetBoundsBundle (X : Type*) where
  cor : Cor312Bounds
  target : ABCTargetData X

theorem bundle_target_height_le {X : Type*} (B : ABCTargetBoundsBundle X) (x : X) :
    B.target.height x ≤ B.target.weight x + B.target.bound :=
  B.target.height_le x

theorem bundle_combined_le_slack {X : Type*} (B : ABCTargetBoundsBundle X) {value : ℚ}
    (h : value ≤ B.cor.combined) : value ≤ B.cor.combined + B.cor.slack :=
  B.cor.combined_le_slack_add h

def abcTargetBoundsRows : List (String × String × String) :=
  [ ("bundle", "ABCTargetBoundsBundle", "DEF (reuses EXIT0 bounds/target)"),
    ("height bound", "bundle_target_height_le", "PROVED (reuse)"),
    ("slack bound", "bundle_combined_le_slack", "PROVED (reuse)"),
    ("scope", "no paper bound proved; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem abcTargetBoundsRows_length : abcTargetBoundsRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ABCTargetBoundsBundleActualAdapted

end
