/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A618ScalingObstructionActual

/-! # A644 (supersedes A618 proof attempt): thin re-export of the GREEN scaling obstruction

The original S1902-`comparisonRegion` proof attempt in this file is RETRACTED: it cited a
nonexistent `comparisonRegion_eq_hull` and would need the comparison region to be
contained in the hull (unavailable: the region is `s1902UnitRegion ∪ {point}`), so
`no_constantRegion_heightComparison` cannot be applied as written.  The valid, green
obstruction is `Mzk1A618ScalingObstructionActual.identity_scaleShift_obstruction`
(unit-region form, gate trio confirmed); this file only re-exports it. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1A618MachineProofActual

export Mzk1A618ScalingObstructionActual (identity_scaleShift_obstruction)

end LeanFormal.IUT.XiFPaper.Mzk1A618MachineProofActual

end
