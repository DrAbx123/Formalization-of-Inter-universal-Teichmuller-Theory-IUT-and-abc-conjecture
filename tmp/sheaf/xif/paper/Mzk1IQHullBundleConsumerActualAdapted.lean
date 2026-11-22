import tmp.sheaf.xif.paper.Mzk1IQHullConsumerActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1IQHullBundleConsumerActualAdapted (adapted copy, A475 reuse) — IQHull interface bundle consumer

Reuses the EXIT0 Mzk1IQHullConsumerActual (hull/unit-region/log-volume reader
bundle) to expose the three IQHull interface facts as standalone projections.
The literal IQ(S±) carrier is still named; this file does not construct it.
No closure; gate NOT PASSED; registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IQHullBundleConsumerActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IQHullConsumerActual

universe u

theorem iqHull_imageSet_le_consumer {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.imageSet ⊆ W.hull :=
  iqHull_imageSet_le W

theorem iqHull_finite_consumer {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.logVolume W.hull < ⊤ :=
  iqHull_finite W

theorem iqHull_bundle_consumer {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.imageSet ⊆ W.hull ∧ W.logVolume W.hull < ⊤ :=
  iqHull_bundle W

def iqHullBundleConsumerRows : List (String × String × String) :=
  [ ("image set <= hull", "iqHull_imageSet_le_consumer", "PROVED (reuse)"),
    ("hull finite", "iqHull_finite_consumer", "PROVED (reuse)"),
    ("bundle", "iqHull_bundle_consumer", "PROVED (reuse)"),
    ("scope", "interface only; literal IQ carrier named; no closure", "INTEGRITY") ]

theorem iqHullBundleConsumerRows_length : iqHullBundleConsumerRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1IQHullBundleConsumerActualAdapted

end
