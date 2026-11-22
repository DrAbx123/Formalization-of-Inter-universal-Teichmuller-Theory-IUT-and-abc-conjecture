/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C3S1902BlockEquivDataActual

/-! # #10: native blockEquiv candidate re-export -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1NativeBlockEquivCandidateActual
open LeanFormal.IUT.XiFPaper.Mzk1C3S1902BlockEquivDataActual
def nativeBlockEquivRows : List (String × String) :=
  [ ("C3S1902BlockEquivData", "tensorIndexEquiv + fiberEquiv + blockEquiv"),
    ("C3S1902BlockEquivDataRequired", "named Nonempty; no inhabitant"),
    ("native candidate", "GAP: no arbitrary Equiv; needs L-side donor") ]
theorem nativeBlockEquivRows_length : nativeBlockEquivRows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1NativeBlockEquivCandidateActual
