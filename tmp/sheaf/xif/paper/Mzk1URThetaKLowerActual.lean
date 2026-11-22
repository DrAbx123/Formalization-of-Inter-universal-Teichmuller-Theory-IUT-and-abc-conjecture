/- U-R C2 J1 (P): thin re-export of the split K-side lower core/bound files.
Kept so external imports of Mzk1URThetaKLowerActual keep working.

THIS FILE ONLY uses maxHeartbeats 1000000 (paper-level budget); RC registry.
-/
import tmp.sheaf.xif.paper.Mzk1URThetaKLowerCoreActual
import tmp.sheaf.xif.paper.Mzk1URThetaKLowerBoundActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerActual

open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerCoreActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerBoundActual

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerActual
end