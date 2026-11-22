import LeanFormal.IUT.Audit.Status

/-! # S3131 mine our own old (b)/(c) attempts before new work - data only -/

namespace LeanFormal.IUT.XiFPaper.S3131OldAttemptsMiningActual

def S3131OldAttemptsMining : List (String × String) :=
  [ ("tmp/sheaf/xif/paper/S2607HeightUpperTargetActual", "HeightUpperTarget def -> reuse shape for (b)"),
    ("tmp/sheaf/xif/paper/S2720BridgeSkeletonActual / S2721BridgeSkeletonActual / S2721BridgeDataActual", "bridge skeletons -> reuse structure/dependency pattern"),
    ("tmp/sheaf/xif/paper/S2722Gap2AssemblyActual", "Gap-2 assembly -> reuse for (c) interface wiring"),
    ("tmp/sheaf/xif/paper/S2722HunitDActual (:44 hunitD, :68 gap2_with_D0)", "hunitD + gap2_with_D0 -> reuse as named D0 supply seam"),
    ("S3131HeightVolumeDictionaryAttemptActual / S3131IUTIVTheorem110InputActual", "our exact remaining (b) statement + Thm 1.10 input shapes -> reuse") ]

theorem S3131OldAttemptsMining_length : S3131OldAttemptsMining.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.S3131OldAttemptsMiningActual